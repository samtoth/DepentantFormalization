{ nixpkgs ? <nixpkgs> }:
with (import nixpkgs {});
agdaPackages.mkDerivation {
  version = "1.0";
  pname = "agda-effects";
  
  src = ./src/..;


  buildInputs = [
  ];

  preBuild = ''
	echo "module Everything where" > Everything.agda
        find src/ -name '*.agda' | sed -e 's/src\///;s/\//./g;s/\.agda$//;s/^/import /' >> Everything.agda
        
  '';

  meta = {};
}
