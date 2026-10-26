{ inputs, ... }:
{
  perSystem =
    { pkgs, lib, ... }:
    {
      devShells =
        let
          devShellEnv =
            {
              compiler ? "gcc",
            }:
            let
              noodler =
                if compiler == "clang" then
                  inputs.self.packages.${pkgs.stdenv.hostPlatform.system}.noodlerClang
                else if compiler == "gcc" then
                  inputs.self.packages.${pkgs.stdenv.hostPlatform.system}.noodlerGcc
                else
                  throw "Invalid compiler value";
            in
            pkgs.mkShell.override
              {
                # Override stdenv in order to change compiler.
                stdenv = noodler.stdenv;
              }
              {
                name = "noodler-${compiler}-dev";

                LD_LIBRARY_PATH = lib.makeLibraryPath [ pkgs.stdenv.cc.cc ];

                shellHook = ''
                  REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || jj root)"
                  export REPO_ROOT

                  # Prepend a clangd allowed to query the dev shells' Nix cc-wrappers for system include
                  # paths. Stock clangd refuses to execute the wrapper named in 'compile_commands.json',
                  # so diagnostics in editors cannot resolve the compiler's bundled headers
                  # (#include <memory>, etc.). Both 'clang' (in the stdenv of the 'clang' dev shell) and
                  # 'clang-tools' ship their own 'clangd', so an entry in buildInputs cannot win;
                  # prepending in shellHook does.
                  export PATH=${
                    lib.makeBinPath [
                      (pkgs.writeShellScriptBin "clangd" ''
                        exec ${lib.getExe' pkgs.clang-tools "clangd"} --query-driver=${
                          lib.escapeShellArg (
                            lib.concatMapStringsSep "," (cc: "${cc}/bin/*") [
                              pkgs.gccStdenv.cc
                              pkgs.clangStdenv.cc
                            ]
                          )
                        } "$@"
                      '')
                    ]
                  }:$PATH
                '';

                # Mata, Catch2, CMake, and Python of the package build, so CMake finds the Nix-built Mata
                # instead of fetching it.
                inputsFrom = [ noodler ];

                buildInputs =
                  with pkgs;
                  [
                    just
                    lldb
                    valgrind

                    clang-tools
                    cppcheck
                    nixd
                    nixfmt
                  ]
                  ++ lib.optionals (lib.meta.availableOn pkgs.stdenv.hostPlatform gdb) [ gdb ];
              };
          clang = devShellEnv { compiler = "clang"; };
          gcc = devShellEnv { compiler = "gcc"; };
        in
        {
          inherit gcc clang;
          default = gcc;
        };
    };
}
