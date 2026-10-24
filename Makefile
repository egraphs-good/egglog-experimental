WWW=${PWD}/target/www/

all: test fixnits nits docs

test:
	cargo nextest run --release
	# nextest doesn't run doctests, so do it here
	cargo test --doc --release

nits:
	@rustup component add clippy
	cargo clippy --tests -- -D warnings
	@rustup component add rustfmt
	cargo fmt --check

fixnits:
	@rustup component add rustfmt
	cargo fmt
	@rustup component add rustfmt
	cargo clippy --fix --tests --workspace --allow-dirty

docs:
	mkdir -p ${WWW}
	cargo doc --no-deps --all-features
	touch target/doc/.nojekyll # prevent github from trying to run jekyll
	cp -r target/doc ${WWW}/docs

# ---------------------------------------------------------------------------
# Protobuf IR codegen. See proto/README.md.
# ---------------------------------------------------------------------------

.PHONY: proto-gen proto-lint proto-test proto-clean

# Include the validation descriptors referenced by the Python bindings.
proto-gen: proto-clean
	uv sync --locked --quiet
	buf generate

proto-lint:
	buf lint
	buf format --diff --exit-code
	buf build

proto-test: proto-gen
	uv run python -m unittest discover -s proto/tests -v

proto-clean:
	# Preserve the handwritten Python/Rust package metadata and root modules.
	rm -rf gen/python/egglog gen/python/buf gen/rust/egglog gen/rust/buf
