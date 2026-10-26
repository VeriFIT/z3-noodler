{ inputs, lib, ... }:
let
  # Flake inputs must be literals, so the Mata tag lives both in flake.nix and in the FetchContent fallback of
  #  CMakeLists.txt. Refuse to evaluate when they drift apart.
  cmakeMataTag =
    let
      tags = lib.concatMap (
        line:
        let
          m = builtins.match "[[:space:]]*GIT_TAG[[:space:]]+([^[:space:]#]+).*" line;
        in
        lib.optional (m != null) (builtins.head m)
      ) (lib.splitString "\n" (builtins.readFile ../CMakeLists.txt));
    in
    lib.throwIfNot (builtins.length tags == 1) "Expected exactly one GIT_TAG in CMakeLists.txt." (
      builtins.head tags
    );
  lock = builtins.fromJSON (builtins.readFile ../flake.lock);
  flakeMataTag = lock.nodes.${lock.nodes.${lock.root}.inputs.mata}.original.ref or null;
in
{
  perSystem =
    { pkgs, ... }:
    let
      version = inputs.self.shortRev or inputs.self.dirtyShortRev or "dev";
      mataPackages =
        lib.throwIfNot (cmakeMataTag == flakeMataTag)
          "Mata version mismatch: CMakeLists.txt uses '${cmakeMataTag}', but the flake input 'mata' is locked to '${toString flakeMataTag}'. Update the 'mata' URL in flake.nix and run 'nix flake lock'."
          inputs.mata.packages.${pkgs.stdenv.hostPlatform.system};

      noodlerGcc = pkgs.callPackage ./package.nix {
        inherit version;
        stdenv = pkgs.gccStdenv;
        mata = mataPackages.mataGcc;
      };
      noodlerClang = pkgs.callPackage ./package.nix {
        inherit version;
        stdenv = pkgs.clangStdenv;
        mata = mataPackages.mataClang;
      };
      noodler = noodlerGcc;
    in
    {
      packages = {
        inherit
          noodler
          noodlerGcc
          noodlerClang
          ;
        default = noodler;
      };

      checks = {
        inherit
          noodlerGcc
          noodlerClang
          ;
      };
    };
}
