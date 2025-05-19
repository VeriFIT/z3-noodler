{
  lib,
  stdenv,
  cmake,
  ninja,
  catch2_3,
  python3,
  fetchFromGitHub,
}:
let
  mata = stdenv.mkDerivation {
    pname = "mata";
    version = "1.15.0";
    src = fetchFromGitHub {
      owner = "VeriFIT";
      repo = "mata";
      rev = "1.15.0";
      hash = "sha256-mo/E+gk/5/56GyWPNbza75hGkPhvvXiGg89htqB4nH8=";
    };

    buildInputs = [
      cmake
      ninja
      python3
    ];
  };
in
stdenv.mkDerivation {
  name = "z3-noodler";

  src = ./.;

  nativeBuildInputs = [
    cmake
    ninja
    python3
    mata
  ];

  buildInputs = [
    catch2_3
  ];
}
