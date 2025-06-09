# Coq Missing Basics

A collection of fundamental lemmas and theorems that require only Coq's standard library - no external dependencies needed.

## Why?

These lemmas exist in various external libraries (stdpp, MathComp, etc.), but accessing them requires:
- Installing and managing dependencies via opam
- Dealing with version compatibility issues  
- Adding heavyweight libraries for just a few basic lemmas
- Learning library-specific conventions and namespaces

This collection provides these essentials using **only** Coq's standard library.

## What's Included

Simple, frequently-needed properties that are surprisingly absent from Coq's standard library:

- **List operations**: `cons_eq`, `filter_length`, `map_compose`, `nth_error_In`
- **Boolean logic**: `iff_and`, `orb_false_eq`, `andb_true_eq`, `xorb` properties
- **Arithmetic**: `plus_le_compat_both`, `mul_cancel_l`, `square_of_sum`
- **Option types**: `option_map_compose`, `Some_inj`
- **Min/Max**: `min_id`, `max_id`
- **Logic**: `curry_uncurry`, `contrapositive`
- **And more...**

## Usage

Simply copy the `.v` files you need into your project. No package manager, no dependencies, no setup.

```coq
Require Import filter_length.
(* Now you can use filter_length lemma directly *)
```

## Philosophy

Sometimes you just need `min n n = n` without installing a 50,000 line library. These lemmas are:
- **Dependency-free**: Uses only Coq's built-in modules
- **Self-contained**: Each file is independent
- **Copy-paste friendly**: Take what you need
- **Beginner-friendly**: No advanced library knowledge required

Perfect for teaching, small projects, or when external dependencies are impractical.

## License

GNU Lesser General Public License Version 2.1
