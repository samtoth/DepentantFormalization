
{ nixpkgs ? <nixpkgs> }:
with (import nixpkgs {});
let
  samlude = import ./../samlude/default.nix {};


  agdaDir = pkgs.stdenv.mkDerivation {
      name = "agdaDir";

      phases = [ "installPhase" ];

      # If you want to add more libraries simply list more in the $out/libraries
      # and $out/defaults folder.
      installPhase = ''
        mkdir $out
        echo "${samlude}/samlude.agda-lib" >> $out/libraries
        echo "samlude" >> $out/defaults
      '';
    };

in
pkgs.mkShell {
  buildInputs = [ pkgs.haskellPackages.Agda ];

  # The build environment's $AGDA_DIR is set through this call.
  AGDA_DIR = agdaDir;
}
