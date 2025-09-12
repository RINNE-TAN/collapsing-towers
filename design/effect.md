# Counterexample

Consider the following program, if we perform the staging, we will observe that:

```ocaml
let x = alloc 13 in
let f = lift (
  lam y.
    let z = store x 17 in
    lift 15
) in
lift (load x)

(* store *)
ϵ
```

```ocaml
let f = (
  lam𝕔 y.
    let z = ⟦store (loc l) 17⟧ in
    lift 15
)
in
lift (load (loc l))

(* store *)
l ↦ 13
```

```ocaml
let f = (
  lam𝕔 y.
    let z = ⟦()⟧ in
    lift 15
)
in
lift (load (loc l))

(* store *)
l ↦ 17
```

```ocaml
code (
  let f₀ = (
    lam x₀.
      let x₁ = 15 in
      x₁
  ) in
  let x₂ = 17 in
  x₂
)

(* store *)
l ↦ 17
```

The input and output programs are not contextual equivalent after erasure:

```ocaml
let x = alloc 13 in
let f = (
  lam y.
    let z = store x 17 in
    15
) in
load x
```

```ocaml
let f₀ = (
  lam x₀.
    let x₁ = 15 in
    x₁
) in
let x₂ = 17 in
x₂

```

It seems that in this step, we performed NbE under a lambda abstraction, but combining NbE with a mutable store might be non-trivial?

```ocaml
let f = (
  lam y.
    let z = ⟦store (loc l) 17⟧ in
    15
)
in 
load (loc l)

(* store *)
l ↦ 13
```

```ocaml
let f = (
  lam y.
    let z = ⟦()⟧ in
    15
)
in
load (loc l)

(* store *)
l ↦ 17
```
