{ inputs, ... }:
{
  flake.overlays.default = final: _prev: {
    noodler = inputs.self.packages.${final.stdenv.hostPlatform.system}.noodler;
    noodlerGcc = inputs.self.packages.${final.stdenv.hostPlatform.system}.noodlerGcc;
    noodlerClang = inputs.self.packages.${final.stdenv.hostPlatform.system}.noodlerClang;
  };
}
