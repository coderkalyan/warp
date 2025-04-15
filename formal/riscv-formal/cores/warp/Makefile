discrete.v:
	cp -ra ../../../../rtl/{*.v,*.sv} .

checks: discrete.v
	python3 ../../checks/genchecks.py
	$(MAKE) -C checks

check: checks

clean:
	rm -f *.v *.sv
	rm -rf checks
