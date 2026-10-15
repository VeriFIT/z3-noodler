#include <algorithm>
#include <chrono>
#include <cctype>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <optional>
#include <random>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

#include <catch2/catch_test_macros.hpp>

#include "util/gparams.h"
#include "util/lbool.h"

#ifndef _WIN32
#include <sys/wait.h>
#endif

namespace {

namespace fs = std::filesystem;

struct model_binding {
    std::string symbol;
    std::string expression;
};

struct smt_case {
    fs::path file;
    lbool expected;
};

std::string read_text_file(const fs::path &p);

class temp_file {
public:
    temp_file(std::string suffix, std::string contents = std::string())
        : m_path(make_unique_path(std::move(suffix))) {
        write(std::move(contents));
    }

    ~temp_file() {
        std::error_code ec;
        fs::remove(m_path, ec);
    }

    const fs::path &path() const { return m_path; }

    void overwrite(std::string contents) {
        write(std::move(contents));
    }

private:
    fs::path m_path;

    static fs::path make_unique_path(std::string suffix) {
        static std::mt19937_64 rng(std::random_device{}());
        auto dir = fs::temp_directory_path();
        for (unsigned attempt = 0; attempt < 256; ++attempt) {
            const auto value = rng();
            auto candidate = dir / ("noodler-e2e-" + std::to_string(value) + suffix);
            std::error_code ec;
            if (fs::exists(candidate, ec)) {
                continue;
            }
            return candidate;
        }
        throw std::runtime_error("Unable to allocate temporary file for noodler e2e tests");
    }

    void write(std::string contents) {
        std::ofstream out(m_path, std::ios::binary | std::ios::trunc);
        if (!out.good()) {
            throw std::runtime_error("Unable to open temporary file: " + m_path.string());
        }
        out << contents;
    }
};

std::string quote_path(const fs::path &p) {
    std::string raw = p.string();
    std::string escaped;
    escaped.reserve(raw.size() + 2);
    escaped.push_back('"');
    for (char ch : raw) {
        if (ch == '\\' || ch == '"') {
            escaped.push_back('\\');
        }
        escaped.push_back(ch);
    }
    escaped.push_back('"');
    return escaped;
}

fs::path detect_z3_binary() {
    if (const char *override_path = std::getenv("NOODLER_E2E_Z3")) {
        fs::path configured(override_path);
        if (fs::exists(configured)) {
            return configured;
        }
        throw std::runtime_error("NOODLER_E2E_Z3 points to missing binary: " + configured.string());
    }

#ifdef _WIN32
    const std::string executable = "z3.exe";
#else
    const std::string executable = "z3";
#endif

    const fs::path cwd = fs::current_path();
    const std::vector<fs::path> candidates = {
        cwd / executable,
        cwd / "z3" / executable,
        cwd.parent_path() / executable,
        cwd.parent_path() / "z3" / executable
    };

    for (const auto &candidate : candidates) {
        if (!candidate.empty() && fs::exists(candidate)) {
            return candidate;
        }
    }

    throw std::runtime_error("Unable to locate z3 binary. Set NOODLER_E2E_Z3 to override.");
}

const fs::path &z3_binary() {
    static const fs::path binary = detect_z3_binary();
    return binary;
}

int normalize_exit_code(int raw_status) {
#ifdef _WIN32
    return raw_status;
#else
    if (raw_status == -1) {
        return raw_status;
    }
    if (WIFEXITED(raw_status)) {
        return WEXITSTATUS(raw_status);
    }
    if (WIFSIGNALED(raw_status)) {
        return 128 + WTERMSIG(raw_status);
    }
    return raw_status;
#endif
}

struct solver_run {
    int exit_code;
    std::string output;
};

solver_run run_z3_process(const fs::path &script) {
    temp_file output_file(".log");
    std::string command = quote_path(z3_binary()) + " smt.string_solver=noodler";
    command += " model=true";
    command += " " + quote_path(script) + " > " + quote_path(output_file.path()) + " 2>&1";
    const int raw_status = std::system(command.c_str());
    solver_run result{normalize_exit_code(raw_status), read_text_file(output_file.path())};
    return result;
}

lbool parse_last_status(const std::string &text) {
    std::istringstream stream(text);
    std::string token;
    bool found = false;
    lbool value = l_undef;
    while (stream >> token) {
        std::transform(token.begin(), token.end(), token.begin(), [](unsigned char c) {
            return static_cast<char>(std::tolower(c));
        });
        if (token == "sat") {
            value = l_true;
            found = true;
        } else if (token == "unsat") {
            value = l_false;
            found = true;
        } else if (token == "unknown") {
            value = l_undef;
            found = true;
        }
    }
    REQUIRE(found);
    return value;
}

std::string augment_with_model_assertions(std::string base_script, const std::vector<std::string> &extra_asserts) {
    if (!base_script.empty() && base_script.back() != '\n') {
        base_script.push_back('\n');
    }
    for (const auto &cmd : extra_asserts) {
        base_script += cmd;
        if (cmd.empty() || cmd.back() != '\n') {
            base_script.push_back('\n');
        }
    }
    base_script += "(check-sat)\n";
    return base_script;
}

std::string trim(std::string_view text) {
    const auto begin = text.find_first_not_of(" \t\r\n");
    if (begin == std::string_view::npos) {
        return "";
    }
    const auto end = text.find_last_not_of(" \t\r\n");
    return std::string(text.substr(begin, end - begin + 1));
}

size_t skip_ws(const std::string &text, size_t pos) {
    while (pos < text.size() && std::isspace(static_cast<unsigned char>(text[pos]))) {
        ++pos;
    }
    return pos;
}

std::string read_quoted_symbol(const std::string &text, size_t &pos) {
    const size_t start = pos;
    ++pos;
    while (pos < text.size()) {
        char c = text[pos++];
        if (c == '\\' && pos < text.size()) {
            ++pos;
            continue;
        }
        if (c == '|') {
            break;
        }
    }
    return text.substr(start, pos - start);
}

std::string read_simple_token(const std::string &text, size_t &pos) {
    const size_t start = pos;
    while (pos < text.size() && !std::isspace(static_cast<unsigned char>(text[pos])) && text[pos] != '(' && text[pos] != ')') {
        ++pos;
    }
    return text.substr(start, pos - start);
}

std::string read_identifier_token(const std::string &text, size_t &pos) {
    pos = skip_ws(text, pos);
    if (pos >= text.size()) {
        return {};
    }
    if (text[pos] == '|') {
        return read_quoted_symbol(text, pos);
    }
    return read_simple_token(text, pos);
}

std::string read_string_literal(const std::string &text, size_t &pos) {
    const size_t start = pos;
    ++pos;
    bool escape = false;
    while (pos < text.size()) {
        const char c = text[pos++];
        if (escape) {
            escape = false;
            continue;
        }
        if (c == '\\') {
            escape = true;
            continue;
        }
        if (c == '"') {
            break;
        }
    }
    return text.substr(start, pos - start);
}

std::string read_balanced_expr(const std::string &text, size_t &pos) {
    const size_t start = pos;
    int depth = 0;
    bool in_string = false;
    bool escape = false;
    while (pos < text.size()) {
        const char c = text[pos++];
        if (in_string) {
            if (escape) {
                escape = false;
                continue;
            }
            if (c == '\\') {
                escape = true;
                continue;
            }
            if (c == '"') {
                in_string = false;
                continue;
            }
            continue;
        }
        if (c == '"') {
            in_string = true;
            continue;
        }
        if (c == '(') {
            ++depth;
            continue;
        }
        if (c == ')') {
            --depth;
            if (depth == 0) {
                break;
            }
        }
    }
    return text.substr(start, pos - start);
}

std::string read_element(const std::string &text, size_t &pos) {
    pos = skip_ws(text, pos);
    if (pos >= text.size()) {
        return {};
    }
    if (text[pos] == '(') {
        return read_balanced_expr(text, pos);
    }
    if (text[pos] == '"') {
        return read_string_literal(text, pos);
    }
    return read_identifier_token(text, pos);
}

std::vector<model_binding> parse_model_from_output(const std::string &text) {
    std::vector<model_binding> bindings;
    const std::string needle = "(define-fun";
    size_t search_pos = 0;
    while (true) {
        size_t def_pos = text.find(needle, search_pos);
        if (def_pos == std::string::npos) {
            break;
        }
        size_t pos = def_pos + needle.size();
        std::string name = read_identifier_token(text, pos);
        if (name.empty()) {
            search_pos = def_pos + needle.size();
            continue;
        }
        std::string args = read_element(text, pos);
        if (trim(args) != "()") {
            search_pos = pos;
            continue;
        }
        std::string sort = read_element(text, pos);
        if (sort.empty()) {
            search_pos = pos;
            continue;
        }
        std::string body = read_element(text, pos);
        if (!body.empty()) {
            bindings.push_back({name, trim(body)});
        }
        search_pos = pos;
    }
    return bindings;
}

std::string read_text_file(const fs::path &p) {
    std::ifstream in(p);
    INFO("Failed to open file: " << p.string());
    REQUIRE(in.good());
    std::ostringstream buffer;
    buffer << in.rdbuf();
    return buffer.str();
}

std::optional<std::string> extract_status_token(const std::string &contents) {
    static const std::regex status_re(R"(\(set-info\s+:status\s+([^\s\)]+)\))", std::regex::icase);
    std::smatch match;
    if (std::regex_search(contents, match, status_re)) {
        std::string token = match[1];
        std::transform(token.begin(), token.end(), token.begin(), [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
        return token;
    }
    return std::nullopt;
}

lbool to_lbool(const std::string &status) {
    if (status == "sat") {
        return l_true;
    }
    if (status == "unsat") {
        return l_false;
    }
    if (status == "unknown") {
        return l_undef;
    }
    FAIL("Unsupported :status value: " << status);
    return l_undef;
}

std::vector<std::string> build_model_assertions(const std::vector<model_binding> &bindings) {
    std::vector<std::string> assertions;
    assertions.reserve(bindings.size());
    for (const auto &binding : bindings) {
        std::ostringstream builder;
        builder << "(assert (= " << binding.symbol << ' ' << binding.expression << "))";
        assertions.push_back(builder.str());
    }
    return assertions;
}

lbool run_with_optional_model(const fs::path &file, const std::vector<std::string> &extra_asserts, std::vector<model_binding> *derived_model = nullptr) {
    std::optional<temp_file> augmented_script;
    const fs::path *script_path = &file;
    if (!extra_asserts.empty()) {
        const std::string base_script = read_text_file(file);
        augmented_script.emplace(".smt2", augment_with_model_assertions(base_script, extra_asserts));
        script_path = &augmented_script->path();
    }

    if (derived_model) {
        derived_model->clear();
    }

    const solver_run result = run_z3_process(*script_path);
    INFO("z3 output for " << script_path->string() << ":\n" << result.output);
    REQUIRE(result.exit_code == 0);
    const lbool status = parse_last_status(result.output);
    if (derived_model && status == l_true) {
        *derived_model = parse_model_from_output(result.output);
    }
    return status;
}

fs::path e2e_dir() {
    fs::path here(__FILE__);
    return here.parent_path() / "e2e";
}

std::vector<smt_case> discover_cases() {
    const fs::path root = e2e_dir();
    INFO("Missing noodler e2e directory: " << root.string());
    REQUIRE(fs::exists(root));
    std::vector<smt_case> cases;
    for (const auto &entry : fs::recursive_directory_iterator(root)) {
        if (!entry.is_regular_file() || entry.path().extension() != ".smt2") {
            continue;
        }
        const std::string contents = read_text_file(entry.path());
        const auto status_token = extract_status_token(contents);
        INFO("Missing (set-info :status ...) in " << entry.path().string());
        REQUIRE(status_token.has_value());
        cases.push_back({entry.path(), to_lbool(*status_token)});
    }
    std::sort(cases.begin(), cases.end(), [](const smt_case &a, const smt_case &b) {
        return a.file < b.file;
    });
    INFO("No SMT2 files discovered under " << root.string());
    REQUIRE(!cases.empty());
    return cases;
}

} // namespace

TEST_CASE("Noodler SMT-LIB end-to-end", "[noodler][smt2][e2e]") {
    gparams::set("smt.string_solver", "noodler");
    const auto cases = discover_cases();

    for (const auto &test : cases) {
        CAPTURE(test.file.string());
        std::vector<model_binding> solver_model;
        const lbool observed = run_with_optional_model(test.file, {}, &solver_model);
        REQUIRE(observed == test.expected);

        if (observed == l_true && !solver_model.empty()) {
            const auto solver_assertions = build_model_assertions(solver_model);
            const lbool round_trip = run_with_optional_model(test.file, solver_assertions);
            REQUIRE(round_trip == l_true);
        }

    }
}

// Issue #480: free positions of the multi var in the length procedure must get the filler
// character, not U+0000 (the push forces the length procedure to answer).
TEST_CASE("Length procedure multi var model has no NUL filler", "[noodler][smt2][e2e]") {
    temp_file script(".smt2",
        "(declare-fun x () String)\n"
        "(declare-fun y () String)\n"
        "(declare-fun z () String)\n"
        "(push 1)\n"
        "(assert (= x (str.++ z \"a\")))\n"
        "(assert (= y (str.++ \"b\" z)))\n"
        "(assert (>= (str.len z) 3))\n"
        "(check-sat)\n"
        "(get-value (x y z))\n");
    const solver_run result = run_z3_process(script.path());
    CAPTURE(result.output);
    REQUIRE(parse_last_status(result.output) == l_true);
    CHECK(result.output.find("\\u{0}") == std::string::npos);
}
