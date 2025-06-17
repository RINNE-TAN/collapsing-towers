# Run Operator

## Small Step

Consider the following program:

```ocaml
let x = print₂ "A" in 
let y = run x in
x +₂ (lift y)
```

After single-step evaluation, it will become:

```ocaml
letc x₀ = print₁ "A" in
let y = run (code x₀) in
(code x₀) +₂ (lift y)
```

If directly execute the run operator, the evaluation will get stuck:

```ocaml
letc x₀ = print₁ "A" in
let y = x₀ in
(code x₀) +₂ (lift y)
```

## Big Step

The big-step semantics implementation of run op:

```scala
case Run(e) => 
    evalmsg(
        env, 
        reifyc({ stFresh = env.length; evalms(env, e) })
    )
```

Current input of `evalmsg` is:

```ocaml
let y = run (code x₀) in
(code x₀) +₂ (lift y)
```

The global state `stBlock` is:

```ocaml
x₀ ↦ print₁ "A"
```

Reification will cause `stBlock` to be executed twice: once during the execution of `Run`, and once during the code generation of `(code x₀) +₂ (lift y)`.
