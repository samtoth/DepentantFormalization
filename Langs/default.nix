{ nixpkgs ? <nixpkgs> }:
with (import nixpkgs {});
let
  samlude = import ./../samlude/default.nix {};
in
agdaPackages.mkDerivation {
  version = "1.0";
  pname = "agda-langs";

  src = ./src/..;


  buildInputs = [
    samlude
  ];

  preBuild = ''
	echo "module Everything where" > Everything.agda
        find src/ -name '*.agda' | sed -e 's/src\///;s/\//./g;s/\.agda$//;s/^/import /' >> Everything.agda
        
  '';

  meta = {};
}
