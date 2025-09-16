Here’s a polished `README.md` draft for your crate:

---

# 🧩 intern — Fast, memory-efficient interning for Rust

`intern` provides a **thread-safe, memory-efficient interning system** for Rust.
It allows you to deduplicate repeated values (like strings, symbols, or AST nodes) by storing them once and reusing references.

Interned values have **pointer identity semantics**: equality and hashing are based on the underlying `Arc<T>` pointer, not just the value.

---

## ✨ Features

* 🔒 **Thread-safe** — sharded lock-based design with low contention.
* ⚡ **Fast lookups** — O(1) average-case insertions using `FxHasher`.
* 🧹 **Automatic cleanup** — unused entries are dropped when no longer referenced.
* 📦 **Flexible** — works with `str`, `String`, `&'static str`, `Rc<str>`, `Arc<str>`, `Box<str>`, and `Cow<str>`.
* 🛠️ **Custom types** — implement `Internable` to intern your own types.
* 🔄 **Serde support** (optional) — enable with `features = ["serde"]`.

---

## 🚀 Example Usage

### Interning strings

```rust
use intern::Interned;

let a = Interned::from("hello");
let b = Interned::from("hello".to_string());

assert!(a.ptr_eq(&b)); // both point to the same Arc<str>
```

### Custom internable type

```rust
use intern::{Internable, Interned, Interner};

#[derive(Eq, Hash, PartialEq)]
struct Symbol(&'static str);

impl Internable for Symbol {
    fn interner() -> &'static Interner<Self> {
        static INTERNER: Interner<Symbol> = Interner::new();
        &INTERNER
    }
}

let a = Symbol("hello").intern();
let b = Symbol("hello").intern();

assert!(a.ptr_eq(&b)); // pointer equality
assert_eq!(a, b);      // value equality still works
```

---

## 🔍 API Overview

### [`Interned<T>`](https://docs.rs/intern/latest/intern/struct.Interned.html)

A wrapper around `Arc<T>` with **pointer identity semantics**.

* `ptr_eq(&self, &Self) -> bool` — fast pointer comparison.
* Implements `Deref`, `Borrow`, `Eq`, `Hash`, `Clone`, `Serialize`/`Deserialize` (with `serde`).

### [`Internable`](https://docs.rs/intern/latest/intern/trait.Internable.html)

A trait for values that can be interned.

* `fn intern(self) -> Interned<Self>` — interns the value.
* `fn interner() -> &'static Interner<Self>` — provides the global interner.

### [`Interner<T>`](https://docs.rs/intern/latest/intern/struct.Interner.html)

Thread-safe storage of interned values.

* `intern(value) -> Interned<T>` — deduplicates or inserts a value.
* `len() -> usize` — number of distinct interned values.
* `is_empty() -> bool`.

---

## ⚙️ Performance

* Sharded `HashMap` reduces lock contention.
* Intern/lookup: **O(1)** average-case.
* Uses `FxHasher` for speed (same as `rustc`).
* Automatically removes unused values when their last reference is dropped.

---

## 📦 Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
intern = "0.1"
```

Optional serde support:

```toml
[dependencies]
intern = { version = "0.1", features = ["serde"] }
```

---

## 🧪 Testing

```sh
cargo test
```

Includes:

* ✅ Deduplication
* ✅ Equality & hashing
* ✅ Automatic cleanup
* ✅ Concurrency stress test

---

## 🔒 Safety

Interned values are stored in `Arc<T>`s.
When the last `Interned<T>` handle drops, the interner removes its entry, ensuring **no leaks** and **safe reuse**.

---

## 📜 License

Licensed under either of:

* MIT License
* Apache License, Version 2.0

at your option.

---
