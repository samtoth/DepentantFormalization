{ nixpkgs ? <nixpkgs> }:
with (import nixpkgs {});
agdaPackages.mkDerivation {
  version = "1.0";
  pname = "samlude";
  
  src = ./src/..;


  buildInputs = [
  ];

  preBuild = ''
	echo "{-# OPTIONS --cubical --cumulativity #-}
module Everything where" > Everything.agda
        find src/ -name '*.agda' | sed -e 's/src\///;s/\//./g;s/\.agda$//;s/^/import /' >> Everything.agda
        
  '';

  meta = {};
}
