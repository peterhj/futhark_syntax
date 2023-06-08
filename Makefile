CARGO := cargo --offline

.PHONY: all test

all: test

test:
	$(CARGO) test --lib -- --nocapture
