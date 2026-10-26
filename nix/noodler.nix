{ inputs, ... }:
{
  perSystem =
    { pkgs, ... }:
    let
      version = inputs.self.shortRev or inputs.self.dirtyShortRev or "dev";
      mataPackages = inputs.mata.packages.${pkgs.stdenv.hostPlatform.system};

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
