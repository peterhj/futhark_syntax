CARGO := cargo

.PHONY: all test

all: test

test:
	$(CARGO) test --lib -- --nocapture
