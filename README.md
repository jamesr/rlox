# rlox

This is a Rust implementation of the Lox language following the delightful
[Crafting Interpreters](https://craftinginterpreters.com/) book. This tries to
stay close to the Java code presented in the book with deviations for taste and
to be Rust-y.  This also adds some unit tests to keep myself honest. All errors
are my own.

## Main repl

The main program follows the Java example closely with the exception of error handling.
Instead of exposing an error reporting function, the main program collects results from
the scanner, etc, and flags errors itself.

## Scanner

The scanner exposes an iterator interface instead of building a collection of tokens
as the book does. The scanner also does not copy the input string but instead produces
tokens containing slices into the input buffer. There is some redundant unicode validity
checking performed in scanning routines. The scanner also yields result types with a line
number and string to report errors.