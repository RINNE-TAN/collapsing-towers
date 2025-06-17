# Semantic Equivalence

Consider the following program:

```ocaml
computeA() # fst
computeB() # snd
computeC() # fst
computeD() # snd
```

If we perform the staging, we will observe that:

```ocaml
# fst stage code generation
computeA()
computeC()

# snd stage code execution
computeB()
computeD()
```

The order of computation is actually different from the execution order by directly erasing the stage annotations, a more specific example is:

1. staging:

    ```ocaml
    (* staging *)
    let x = print₁ "A" in
    let y = print₂ "B" in
    let z = print₁ "C" in
    x
    
    (* fst stage output *)
    ∅
    (* snd stage output *)
    ∅
    ```

    ```ocaml
    (* code generation *)
    code(let x₀ = print₁ "B" in x₀)
    
    (* fst stage output *)
    "A"
    "C"
    (* snd stage output *)
    ∅
    ```

    ```ocaml
    (* code execution *)
    unit
    
    (* fst stage output *)
    "A"
    "C"
    (* snd stage output *)
    "B"
    ```

2. erasing:

    ```ocaml
    (* erasing *)
    let x = print "A" in
    let y = print "B" in
    let z = print "C" in
    x
    
    (* output *)
    ∅
    ```

    ```ocaml
    (* execution *)
    unit
    
    (* output *)
    "A"
    "B"
    "C"
    ```

If we have a `run` operator, the order of computation becomes more complex.
