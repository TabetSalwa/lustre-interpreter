# Lustre Interpreter in Rocq

This repository contains a Rocq formalization of a small interpreter for a Lustre-like synchronous language.  
The project focuses on defining a clean operational semantics for synchronous streams and implementing it as an executable interpreter in Rocq.

The main goal is not completeness with respect to the full Lustre language, but rather to capture its core synchronous execution model (logical instants, streams, temporal operators) in a precise and modular way.

---

## Project overview

The interpreter follows a classical compiler pipeline:

1. **Front-end**  
   Lexing, parsing, and abstract syntax.
2. **Runtime semantics**  
   Values, environments, state, and memory for temporal operators.
3. **Interpreter**  
   Evaluation of expressions and nodes, tick by tick.
4. **Proof infrastructure**  
   Auxiliary lemmas supporting reasoning about the interpreter.

The design emphasizes:
- explicit logical time,
- deterministic synchronous execution,
- separation between value computation and state update.

---

## File structure

### Front-end

- `lexer.v`  
  Tokenization of source programs.

- `ast.v`  
  Abstract syntax tree for the Lustre subset (types, expressions, equations, nodes).

- `parser.v`  
  Recursive-descent parser from tokens to AST.

---

### Runtime semantics

- `semantics.v`  
  Runtime objects used by the interpreter:
  values, optional values (presence/absence),
  environments, delay memory, and interpreter state.

---

### Expression evaluation

- `eval_expr.v`  
  Evaluation of expressions at a single logical instant.
  Handles:
  - pure expressions,
  - temporal operators (`pre`, `fby`, `->`),
  - clocked constructs (`when`, `merge`),
  - node calls.

  The evaluator carefully maintains alignment of delay memory and call state,
  using explicit skipping for untaken branches.

- `EvalExprLemmas.v`  
  Lemmas about expression evaluation, including invariants relating
  evaluation, skipping, and resource consumption.

---

### Node evaluation

- `eval_node.v`  
  Evaluation of nodes for one logical instant.
  Node execution is split into two phases:
  1. **Phase A:** compute all values for the current instant.
  2. **Phase B:** update the internal state for the next instant.

  This structure reflects the synchronous reaction model of Lustre and
  avoids double evaluation of temporal constructs and node calls.

---

### Proof support

- `EnvLemmas.v`  
  Basic lemmas about environments (lookup, update, extension),
  used throughout the interpreter.

---

## Execution model

Programs are executed tick by tick:
- at each logical instant, inputs are provided,
- expressions and equations are evaluated synchronously,
- outputs are produced,
- the internal state is updated for the next instant.

Multi-tick execution is obtained by iterating single-tick evaluation.

---

## Scope and limitations

This project implements a subset of Lustre, chosen to illustrate:
- synchronous streams,
- temporal operators,
- clocked expressions,
- node calls and stateful execution.

It does not aim to cover the full Lustre language, nor to provide
advanced static analyses such as causality or clock checking.
These aspects are deliberately kept out of scope.

---

## Context

This project was developed as part of the **SYNC course** (MPRI),
with the goal of exploring the operational semantics of synchronous languages
and their formalization in Rocq.

---

## Author

Salwa Tabet Gonzalez  
