# `cw_storage_macros`

This crate provides macros for storage operations in CosmWasm smart contracts.

## Features

- Macros for simplified storage operations in CosmWasm contracts.
- Built-in caching for optimized read operations.
- Auto-generated tests for each macro usage.

## Macros

- `item!`: Manages single storage items.
- `map!`: Handles key-value pairs in storage.
- `example_key!`: Utility for defining example keys for non-string or numeric keyed maps for use in generated tests.

## Usage

Check out `tests/it.rs` & run `cargo test`
