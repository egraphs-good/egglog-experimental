WWW=${PWD}/target/www/

all: test fixnits nits docs

test:
	cargo nextest run --release --features typed
	# nextest doesn't run doctests, so do it here
	cargo test --doc --release --features typed
	cargo check --no-default-features
	cargo check --no-default-features --features typed --examples
	cargo test --release --no-default-features --features typed --test typed_examples

nits:
	@rustup component add clippy
	cargo clippy --tests --examples --features typed -- -D warnings
	@rustup component add rustfmt
	cargo fmt --check

fixnits:
	@rustup component add rustfmt
	cargo fmt
	@rustup component add rustfmt
	cargo clippy --fix --tests --examples --workspace --features typed --allow-dirty

docs:
	mkdir -p ${WWW}
	cargo doc --no-deps --all-features
	touch target/doc/.nojekyll # prevent github from trying to run jekyll
	cp -r target/doc ${WWW}/docs
