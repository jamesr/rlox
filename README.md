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

## AST

The abstract syntax tree uses Rust's enum and struct types and
are hand written. The book uses Java's dynamic type system and
a code generation mechanism for these. The Rust types could probably be generated more easily using macros. The AST currently defines a single visitor type for both expressions and statements and does not have a way for the expression visitor to return any side effects. This will need to change to generate and handle errors during evaluation.

Expressions contain an embedded identifier which is used during the resolution
and execution passes to resolve variable lookups to the correct scope.

## Parser

The parser generally follows the book except that it uses Rust's result types
instead of exceptions and error reporting functions. The parser attempts to
synchronize after errors inside statements and then returns the original error.