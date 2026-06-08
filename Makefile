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
