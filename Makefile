PYTHON ?= python3

.PHONY: audit build reproduce clean

audit:
	$(PYTHON) scripts/audit_formal_sources.py

build:
	lake build

reproduce: audit build

clean:
	lake clean
	rm -f formal-source-hashes.json
