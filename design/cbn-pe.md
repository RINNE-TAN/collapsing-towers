# CBN Partial Evaluation

Considering restricting the `lift` operation to `CBN` semantics, when lifting a function, the corresponding second-stage code for the function is generated at the call site based on the current context.

```ocaml
let f : <int> → <int> = λ(x).x +₂ x in
let f : <int → int> = lift(f) in
f @₂ lift(0);
f @₂ lift(1);
f @₂ lift(2);
```

However, such a `lift` operation breaks the original purpose of using this operation: to generate a second-stage function that can be reused.

```ocaml
code {
  (* 1st *)
  let x₀ = 0 in
  let f₀ = 
    λ(x).
      let y = x + x in 
      y 
  in
  f₀ @ x₀;
  (* 2nd *)
  let x₁ = 1 in
  let f₁ = 
    λ(x).
      let y = x + x in 
      y 
  in
  f₁ @ x₁;
  (* 3rd *)
  let x₂ = 2 in
  let f₂ = 
    λ(x).
      let y = x + x in 
      y 
  in
  f₂ @ x₂;
}
```

In fact, if code reuse is not needed, it can be entirely achieved through substitution in the first stage.

```ocaml
let f : <int> → <int> = λ(x).x +₂ x in
f @ lift(0);
f @ lift(1);
f @ lift(2);
```

```ocaml
code {
  (* 1st *)
  let x₀ = 0 in
  let y₀ = x₀ + x₀ in
  y₀;
  (* 2nd *)
  let x₁ = 1 in
  let y₁ = x₁ + x₁ in
  y₁;
  (* 3rd *)
  let x₂ = 2 in
  let y₂ = x₂ + x₂ in
  y₂;
}
```

The evaluation process under two cases:

```ocaml
(* input *)
lift(λ(x).x +₂ x) @₂ lift(0)

(* lam𝕔 *)
λ𝕔(x).code(x) +₂ code(x) @₂ lift(0)

(* lam body specialization *)
λ𝕔(x).code(let y = x + x in y) @₂ lift(0)

(* output *)
code {
  let x₀ = 0 in
  let f₀ = 
    λ(x).
      let y = x + x in 
      y 
  in
  f₀ @ x₀
}
```

```ocaml
(* input *)
(λ(x).x +₂ x) @₂ lift(0)

(* let𝕔 *)
let𝕔 x₀ = 0 in
(λ(x).x +₂ x) @₂ code(x₀)

(* subst *)
let𝕔 x₀ = 0 in
code(x₀) +₂ code(x₀)

(* lam body specialization *)
let𝕔 x₀ = 0 in
code {
  let y₀ = x₀ + x₀ in 
  y₀
}

(* output *)
code {
  let x₀ = 0 in
  let y₀ = x₀ + x₀ in 
  y₀
}
```
