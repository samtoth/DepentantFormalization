{ nixpkgs ? <nixpkgs> }:
with (import nixpkgs {});
let
  onelab = import ./nix/1lab-master.nix;
in
agdaPackages.mkDerivation {
  version = "1.0";
  pname = "tts";
  
  src = ./src;


  buildInputs = [ onelab
  ];

  preBuild = ''
	echo "module Everything where" > Everything.agda
        find src/ -name '*.agda' | sed -e 's/src\///;s/\//./g;s/\.agda$//;s/^/import /' >> Everything.agda
        
  '';

  meta = {};
}
