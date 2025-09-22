.PHONY: build axioms clean

build:
	cd no-zeros && lake update && lake build

axioms:
	cd no-zeros && ~/.elan/bin/lake build +rh.Proof.AxiomsCheck

clean:
	rm -rf no-zeros/.lake

