coverage:
	cargo install cargo-tarpaulin
	cargo tarpaulin --target-dir tarpaulin --out Html
