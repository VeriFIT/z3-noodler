{
  lib,
  stdenv,
  cmake,
  python3,
  catch2_3,
  mata,
  version ? "dev",
}:
stdenv.mkDerivation {
  pname = "z3-noodler";
  inherit version;

  src =
    let
      root = ./..;
    in
    with lib.fileset;
    toSource {
      inherit root;
      fileset = intersection (gitTracked root) (unions [
        ../CMakeLists.txt
        ../z3.pc.cmake.in
        ../cmake
        ../scripts
        ../src
      ]);
    };

  # Nix passes absolute install directories, which 'z3.pc' would prefix once more.
  postPatch = ''
    substituteInPlace z3.pc.cmake.in \
      --replace-fail '$'{exec_prefix}/@CMAKE_INSTALL_LIBDIR@ @CMAKE_INSTALL_FULL_LIBDIR@ \
      --replace-fail '$'{prefix}/@CMAKE_INSTALL_INCLUDEDIR@ @CMAKE_INSTALL_FULL_INCLUDEDIR@
  '';

  nativeBuildInputs = [
    cmake
    python3
  ];

  buildInputs = [
    mata
    catch2_3
  ];

  cmakeFlags = [
    # Mata comes from Nix; never fall back to fetching it.
    "-DFETCHCONTENT_FULLY_DISCONNECTED=ON"
    # The source is not a Git checkout.
    "-DZ3_INCLUDE_GIT_HASH=OFF"
    "-DZ3_INCLUDE_GIT_DESCRIBE=OFF"
    "-DZ3_ENABLE_EXAMPLE_TARGETS=OFF"
  ];

  doCheck = true;

  # The end-to-end tests run the 'z3' binary from the build directory.
  checkPhase = ''
    runHook preCheck
    make -j"$NIX_BUILD_CORES" test-noodler
    ./test-noodler
    runHook postCheck
  '';

  meta = {
    description = "An SMT solver for string constraints";
    homepage = "https://github.com/VeriFIT/z3-noodler";
    license = lib.licenses.mit;
    platforms = lib.platforms.unix;
    mainProgram = "z3";
  };
}
