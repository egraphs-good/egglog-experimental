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

.PHONY: proto-gen proto-lint proto-clean proto-drift

# Include the validation descriptors referenced by the Python bindings.
proto-gen:
	uv sync --quiet
	buf generate --include-imports

proto-lint:
	buf lint
	buf format --diff --exit-code
	buf build

proto-clean:
	# Preserve the handwritten Python/Rust package metadata and root modules.
	rm -rf gen/python/egglog gen/python/buf gen/rust/egglog gen/rust/buf

# `gen/` is committed, so it can drift from the schema. This fails if it has.
proto-drift: proto-gen
	git diff --exit-code -- gen
