PYTHON ?= python3

.PHONY: audit cache build reproduce clean

audit:
	$(PYTHON) scripts/audit_formal_sources.py

cache:
	lake exe cache get

build:
	lake build

reproduce: audit cache build

clean:
	lake clean
	rm -f formal-source-hashes.json
