all:
	dune build

# Uncomment this once ready, you can add more tests here
test:
	cat proofs/k.proof | dune exec ./prover.exe
	cat proofs/app.proof | dune exec ./prover.exe
	cat proofs/comp.proof | dune exec ./prover.exe
	cat proofs/appid.proof | dune exec ./prover.exe
