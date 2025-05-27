# Code Reference

## Reification

Consider the following typing rules: `f`, `arg`, `cond`, `b0`, and `b1` are all of type rep. Intuitively, they should have similar behavior.

```math
\frac
{
\Gamma \vdash f : \langle \tau_a \rightarrow  \tau_b \rangle, 
\Gamma \vdash arg : \langle \tau_a \rangle
}
{
\Gamma \vdash app_2 \ f \ arg : \langle \tau_b \rangle
}
```

```math
\frac
{
\Gamma \vdash cond : \langle bool \rangle, 
\Gamma \vdash b_0 : \langle \tau \rangle,
\Gamma \vdash b_1 : \langle \tau \rangle
}
{
\Gamma \vdash if_2 \ cond \ b_0 \ b_1 : \langle \tau \rangle
}
```

```scala
case App2(f, arg) =>
    val Code(f) = evalms(env, f)
    val Code(arg) = evalms(env, arg)
    reflect(App1(f, arg))
case If2(cond, b0, b1) =>
    val Code(cond) = evalms(env, cond)
    val Code(b0) = reify(evalms(env, b0))
    val Code(b1) = reify(evalms(env, b1))
    reflect(If1(cond, b0, b1))
```

In `b0` and `b1`, a `reify` operation will actually be inserted. Currently, this is ensured through `R(Reify) Context`.

```math
R(X) ::= 
\text{Lam}_c(f, x, X) \; | \; 
\text{If}(\text{Code}(e), X, e) \; | \; 
\text{If}(\text{Code}(e), v, X) \; | \; 
\text{Run}(X) \; | \; 
\text{Let}_c(x, e, X)
```

Consider the `reflect` and `reify` head step rules: it locates the nearest reify operation and simulates a code store through let insertion. When encountering a reify operation, it extracts all the code bindings stored in the store and reifies them into the code.

```math
P [E[\text{Reflect}(e)]]
\longrightarrow 
P [\text{Let}_c(x, e, E[\text{Code}(x)])] \quad 
\text{where } x \text{ is fresh}
```

```math
M[\text{Let𝕔} (x, e_1, \text{Code}(e_2))] 
\rightarrow 
M[\text{Code}(\text{Let}(x, e_1, e_2))]
```

However, this introduces an additional requirement: the reify operation and the result must be under another `R` context or `hole` context, otherwise, the following issue may arise:

```ocaml
(* reify under B context *)
let x = (letc x0 = eff in (code x0)) in
0

(* reify result under B context *)
let x = (code (let x0 = eff in x0)) in
0

(* side effect discard *)
0
```

However, in some cases, the code appearing under the B context is valid, as shown below:

```ocaml
(* code duplicate *)
letc x0 = eff in
plus2 (code x0) (code x0)

(* code discard *)
letc x0 = eff in
let x = (code x0) in
0
```

Therefore, the code here should be divided into two types:

- Code Reference: This represents a reference to a piece of code, which can be duplicated or discarded. For example, `code x0` under let insertion.
- Actual Code: This represents the real code, whose behavior should be linear. For example, the reify result `code (let x0 = eff in x0)`.

## Phase Consistency Principle

We now have two level of bindings, `letc` and `lets`, which require their reference levels to correspond to their definition levels. This aligns with the `Phase Consistency Principle` mentioned in *A Practical Unification of Multi-stage Programming and Macros* (using different notations). Some counterexamples are as follows:

```ocaml
(* stuck *)
letc x (* phase 2 *) = eff in
x (* phase 1 *)

(* cross stage persistence *)
let x (* phase 1 *) = ref 0 in
code x (* phase 2 *)
```
