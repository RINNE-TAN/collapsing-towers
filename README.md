# OOPSLA 2026 Artifact

Name: **When Do Staging Annotations Preserve Semantics? Mechanizing Typed Semantics-Preserving Multi-Stage Programming with Let-Insertion**

## Paper Summary

Multi-stage programming allows programmers to write code that generates code,
improving performance through specialization. However, staging annotations that
control evaluation order can inadvertently change program semantics. The paper
asks: **when do staging annotations preserve the semantics of the original
unstaged program?**

To answer this, the paper develops two typed two-stage calculi:

- **λ|2|** — a calculus with general recursion and automatic let-insertion, where a lightweight
  type-and-effect system tracks code-generation effects.
- **λ|2|^ref** — an extension with second-stage mutable references, using a
  Kripke world model to relate stores across runs.

The key result is the guarantee of **semantics preservation**: if a well-typed 
two-stage program evaluates to a code value, the generated code is contextually 
equivalent to the stage-erased original. This is proved via step-indexed binary 
logical relations.

## Calculus Variants

| Paper Name | Lean Module | Description |
|---|---|---|
| - | `Instar.TwoLevelBasic` | Base two-stage calculus (pure, no side effects) |
| λ\|2\| | `Instar.TwoLevelRec` | Extended calculus with general recursion |
| - | `Instar.TwoLevelMut` | Extended calculus with mutable references |
| λ\|2\|^ref | `Instar.TwoLevelFinal` | Extended calculus with general recursion and mutable references |

`Instar.TwoLevelBasic` and `Instar.TwoLevelMut` are intermediate variants.

---

## Reproducibility

### 1. Build & Compilation Instructions

#### VirtualBox VM (Recommended)

We provide a VirtualBox virtual machine image (OVA 1.0 standard) with
everything pre-installed:

| Item | Value |
|---|---|
| Guest OS | Ubuntu 22.04 |
| Username | `artifact` |
| Password | `artifact` |

The VM contains the full Lean / mathlib4 environment together with the
source code of this artifact, so no additional setup is required —
after importing the OVA and logging in, you can build and verify the
artifact directly.

If you prefer to set up the environment manually, follow the
instructions below.

#### Verified Environment

| Component | Version |
|---|---|
| Lean | 4.29.0-rc2 (`leanprover/lean4:v4.29.0-rc2`) |
| Lake (build tool) | bundled with Lean 4.29.0 |
| mathlib4 | `abc669d11b88e163aed1c05b352b5b16889c4ad8` |

Dependency versions are pinned in `lake-manifest.json`.

#### Quick Start

```bash
# 1. Install elan
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source $HOME/.elan/env

# 2. Install Lean 4.29.0-rc2 via elan
elan toolchain install leanprover/lean4:v4.29.0-rc2
elan default leanprover/lean4:v4.29.0-rc2

# 3. Enter the directory
cd artifact

# 4. Fetch and build dependencies (mathlib4), then build all formalizations
lake build Instar.TwoLevelBasic.Defs Instar.TwoLevelRec.Defs Instar.TwoLevelMut.Defs Instar.TwoLevelFinal.Defs
```

For individual builds:

```bash
lake build Instar.TwoLevelBasic.Defs    # Basic calculus
lake build Instar.TwoLevelRec.Defs      # λ|2|, extended calculus with general recursion
lake build Instar.TwoLevelMut.Defs      # Extended calculus with mutable references
lake build Instar.TwoLevelFinal.Defs    # λ|2|^ref, extended calculus with general recursion and mutable references
```

#### Artifact Verification

```bash
lake build Instar.TwoLevelBasic.Defs Instar.TwoLevelRec.Defs Instar.TwoLevelMut.Defs Instar.TwoLevelFinal.Defs
```
A clean build of all four variants confirms all proofs are complete.

#### Build Output

Each variant's `Defs.lean` contains `#check` commands that print the type
signature of every key theorem during compilation:

```
lake build Instar.TwoLevelBasic.Defs
info: Instar/TwoLevelBasic/Defs.lean:14:0: progress ...
info: Instar/TwoLevelBasic/Defs.lean:15:0: preservation ...
...
info: Instar/TwoLevelBasic/Defs.lean:29:0: semantics_preservation.stepn.rep ...
Build completed successfully (410 jobs).

lake build Instar.TwoLevelRec.Defs
...
Build completed successfully (412 jobs).

lake build Instar.TwoLevelMut.Defs
...
Build completed successfully (411 jobs).

lake build Instar.TwoLevelFinal.Defs
...
Build completed successfully (419 jobs).
```

---

### 2. Paper-to-Artifact Correspondence

The mechanization covers **all theorems** stated in the paper.

#### Surface Syntax of λ|2| (Fig. 2)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Term `t` | `Expr` (inductive type) | [`Syntax/Basic.lean`](Instar/TwoLevelRec/Syntax/Basic.lean) |
| `()`, `n`, `x`, `λx.t`, `let x = t₁ in t₂` | `.unit`, `.lit n`, `.fvar x`, `.lam e`, `.lets b e` | same |
| `lift t` | `.lift e` | same |
| `run t` | `.run e` | same |
| `app^s t₁ t₂` | `.app₁ e₁ e₂` / `.app₂ e₁ e₂` | same |
| `fix^s t` | `.fix₁ e` / `.fix₂ e` | same |
| `ifz^s t₁ t₂ t₃` | `.ifz₁ e₁ e₂ e₃` / `.ifz₂ e₁ e₂ e₃` | same |
| `t₁ ⊕^s t₂` | `.binary₁ op e₁ e₂` / `.binary₂ op e₁ e₂` | same |

#### Administrative Syntax & Reduction of λ|2| (Fig. 3)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Administrative term `g` | Constructors of `Expr` (`code`, `reflect`, `lam𝕔`, `lets𝕔`) | [`Syntax/Basic.lean`](Instar/TwoLevelRec/Syntax/Basic.lean) |
| Value `v` | `value : Expr → Prop` (inductive predicate) | [`OperationalSemantics/Value.lean`](Instar/TwoLevelRec/OperationalSemantics/Value.lean) |
| Pure frame `B`, Pure context `E` | `ctx𝔹`, `ctx𝔼` | [`OperationalSemantics/EvalCtx.lean`](Instar/TwoLevelRec/OperationalSemantics/EvalCtx.lean) |
| Reification frame `R`, context `P` | `ctxℝ`, `ctxℙ` | same |
| Evaluation context `M` | `ctx𝕄` | same |
| Head reduction `t ↝ t'` | `e₀ ↝ e₁` (notation for `head e₀ e₁`) | [`OperationalSemantics/SmallStep.lean`](Instar/TwoLevelRec/OperationalSemantics/SmallStep.lean) |
| Single-step reduction `t ⭢ t'` | `e₀ ⭢ e₁` (notation for `step_lvl 0 e₀ e₁`) | same |
| Multi-step reduction `t ⭢* t'` | `e₀ ⭢* e₁` (notation for `stepn`) | same |

#### Static Semantics: Types, Effects, Well-Formedness of λ|2| (Figs. 4-5)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Type `τ` | `Ty` (inductive type) | [`SyntacticTyping/Ty.lean`](Instar/TwoLevelRec/SyntacticTyping/Ty.lean) |
| `nat`, `unit` | `.nat`, `.unit` | same |
| `τ₁ →^ε τ₂` | `.arrow τ₁ τ₂ ε` | same |
| `rep τ` | `.rep τ` | same |
| `frag τ` | `.fragment τ` | same |
| Effect `ε` ∈ {⊥, ⊤} | `Effect` enum (`⊥` / `⊤`) | [`SyntacticTyping/Effect.lean`](Instar/TwoLevelRec/SyntacticTyping/Effect.lean) |
| Effect lattice ⊑, ⊔ | `Effect.le` (≤), `Effect.union` (∪) | same |
| Typing context `Γ` | `TEnv` (list of `Ty × Stage`) | [`SyntacticTyping/Env.lean`](Instar/TwoLevelRec/SyntacticTyping/Env.lean) |
| Well-formed type `WF^s τ` | `wbt s τ` | [`SyntacticTyping/Ty.lean`](Instar/TwoLevelRec/SyntacticTyping/Ty.lean) |

#### Typing Judgments of λ|2| (Figs. 6-7)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| `Γ ⊢ t : τ ∣ ε` | `typing_reification Γ e τ ε` | [`SyntacticTyping/Typing.lean`](Instar/TwoLevelRec/SyntacticTyping/Typing.lean) |
| `Γ ⊢^s t : τ ∣ ε` | `typing Γ s e τ ε` | same |

#### Erasure of λ|2| (Fig. 8)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Term erasure `⎸t⎹` | `⎸e⎹` (notation for `erase`) | [`Syntax/Transform.lean`](Instar/TwoLevelRec/Syntax/Transform.lean) |
| Type erasure `⎸τ⎹` | `erase_ty τ` | [`SyntacticTyping/Ty.lean`](Instar/TwoLevelRec/SyntacticTyping/Ty.lean) |
| Environment erasure `⎸Γ⎹` | `erase_env Γ` | [`SyntacticTyping/Env.lean`](Instar/TwoLevelRec/SyntacticTyping/Env.lean) |

#### Contextual Equivalence of λ|2|↓ (Fig. 9)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Observational context `C` | `ObsCtxℂ` | [`CtxEquiv/ObsCtx.lean`](Instar/TwoLevelRec/CtxEquiv/ObsCtx.lean) |
| Basic observation frame `F` | `ObsCtx𝔽` | same |
| Context typing `C : (Γ ⊢ τ) ⇒ (Γ' ⊢ τ')` | `ObsCtxℂ Γ τ C Γ' τ'` | same |
| Contextual approx. `Γ ⊨ t₁ ≼𝑐𝑡𝑥 t₂ : τ` | `ctx_approx` | same |
| Contextual equiv. `Γ ⊨ t₁ ≃𝑐𝑡𝑥 t₂ : τ` | `ctx_equiv` | same |

#### Binary Logical Relations of λ|2|↓ (Fig. 10)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Value interpretation `(k, v₀, v₁) ∈ 𝒱⟦τ⟧` | `log_approx_value k v₀ v₁ τ` | [`LogicalEquiv/LogicalRelation.lean`](Instar/TwoLevelRec/LogicalEquiv/LogicalRelation.lean) |
| Term interpretation `(k, e₀, e₁) ∈ ℰ⟦τ⟧` | `log_approx_expr k e₀ e₁ τ` | same |
| Environment interpretation `(k, γ₀, γ₁) ∈ 𝒢⟦Γ⟧` | `log_approx_env k γ₀ γ₁ Γ` | same |
| Logical approx. `Γ ⊨ t₁ ≼𝑙𝑜𝑔 t₂ : τ` | `log_approx Γ e₀ e₁ τ` | same |
| Logical equiv. `Γ ⊨ t₁ ≃𝑙𝑜𝑔 t₂ : τ` | `log_equiv Γ e₀ e₁ τ` | same |

#### Theorems of λ|2|

The table below maps every theorem and key lemma from the paper to the Lean code.

| # | Paper Theorem / Lemma | Lean Identifier | File (TwoLevelRec) |
|---|---|---|---|
| Lemma 3.1 | Deterministic Decomposition | `deterministic.decomposition_ctxℙ` | [`OperationalSemantics/Deterministic.lean`](Instar/TwoLevelRec/OperationalSemantics/Deterministic.lean) |
| Theorem 3.2 | Determinism | `deterministic` | same |
| Lemma 3.3 | Strengthened Progress | `progress.strengthened` | [`SyntacticSoundness/Progress.lean`](Instar/TwoLevelRec/SyntacticSoundness/Progress.lean) |
| Theorem 3.4 | Progress | `progress` | same |
| Theorem 3.5 | Open Substitution | `preservation.open_subst` | [`SyntacticSoundness/PresvOpenSubst.lean`](Instar/TwoLevelRec/SyntacticSoundness/PresvOpenSubst.lean) |
| Theorem 3.6 | Preservation | `preservation` | [`SyntacticSoundness/Preservation.lean`](Instar/TwoLevelRec/SyntacticSoundness/Preservation.lean) |
| — | Multi-step Preservation | `preservation.stepn` | same |
| — | Type Soundness | `soundness` | [`SyntacticSoundness/Soundness.lean`](Instar/TwoLevelRec/SyntacticSoundness/Soundness.lean) |
| Theorem 4.1 | Syntactic Erasure Soundness | `typing.erase.safety` | [`SyntacticTyping/EraseSafety.lean`](Instar/TwoLevelRec/SyntacticTyping/EraseSafety.lean) |
| Theorem 5.3 | Transitivity of Contextual Equiv. | `ctx_equiv.trans` | [`CtxEquiv/Transitivity.lean`](Instar/TwoLevelRec/CtxEquiv/Transitivity.lean) |
| Theorem 5.4 | Fundamental Property | `log_equiv.fundamental` | [`LogicalEquiv/Fundamental.lean`](Instar/TwoLevelRec/LogicalEquiv/Fundamental.lean) |
| Theorem 5.5 | Soundness of Logical Relations | `log_equiv.soundness` | [`LogicalEquiv/Soundness.lean`](Instar/TwoLevelRec/LogicalEquiv/Soundness.lean) |
| Lemma 5.6 | Sem. Pres. of Substitution | `semantics_preservation.lets` | [`SemanticsPreservation/PresvPure.lean`](Instar/TwoLevelRec/SemanticsPreservation/PresvPure.lean) |
| Lemma 5.7 | Sem. Pres. of Let-Insertion | `semantics_preservation.reflect.head` | [`SemanticsPreservation/PresvReflect.lean`](Instar/TwoLevelRec/SemanticsPreservation/PresvReflect.lean) |
| Theorem 5.8 | Sem. Pres. of Single-Step Reduction | `semantics_preservation` | [`SemanticsPreservation/Preservation.lean`](Instar/TwoLevelRec/SemanticsPreservation/Preservation.lean) |
| Theorem 5.9 | Strengthened Sem. Preservation | `semantics_preservation.stepn` | same |
| Theorem 5.10 | Semantics Preservation | `semantics_preservation.stepn.rep` | same |

#### λ|2|^ref — Extension with Mutable References

λ|2|^ref extends λ|2| with second-stage mutable references. The first stage
remains store-pure; store effects are confined to generated code. A Kripke
world model relates stores across two program runs in the logical relation.

##### Extended Syntax & Dynamic Semantics & Static Semantics (Fig. 11)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Location `ℓ` | `.loc n` (constructor of `Expr`) | [`Syntax/Basic.lean`](Instar/TwoLevelFinal/Syntax/Basic.lean) |
| `alloc^s t`, `get^s t`, `put^s t₁ t₂` | `.alloc₁`, `.alloc₂`, `.get₁`, `.get₂`, `.put₁`, `.put₂` | same |
| Store `σ` | `Store` (list of `Expr`) | [`OperationalSemantics/Store.lean`](Instar/TwoLevelFinal/OperationalSemantics/Store.lean) |
| Store-related reduction `⟨σ, t⟩ → ⟨σ', t'⟩` | `step_lvl` extended with store | [`OperationalSemantics/SmallStep.lean`](Instar/TwoLevelFinal/OperationalSemantics/SmallStep.lean) |
| Reference type `ref τ` | `.ref τ` (constructor of `Ty`) | [`SyntacticTyping/Ty.lean`](Instar/TwoLevelFinal/SyntacticTyping/Ty.lean) |
| Store-free assertion | `store_free : Expr → Prop` | [`Syntax/Grounded.lean`](Instar/TwoLevelFinal/Syntax/Grounded.lean) |

##### World Model & Kripke Logical Relations (Fig. 12)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| World `𝓦 ⊆ ℕ × ℕ` | `World` (partial bijection on locations) | [`LogicalEquiv/World.lean`](Instar/TwoLevelFinal/LogicalEquiv/World.lean) |
| World extension `𝓦' ⊒ 𝓦` | `World.future` (notation `𝓦' ⊒ 𝓦`) | same |
| Store agreement `(σ₁, σ₂) : 𝓦` | `log_well_store 𝓦 σ₁ σ₂` | [`LogicalEquiv/LogicalRelation.lean`](Instar/TwoLevelFinal/LogicalEquiv/LogicalRelation.lean) |
| Value interpretation `(k, 𝓦, v₀, v₁) ∈ 𝒱⟦τ⟧` | `log_approx_value (k, 𝓦) v₀ v₁ τ` | same |
| Term interpretation `(k, 𝓦, e₀, e₁) ∈ ℰ⟦τ⟧` | `log_approx_expr (k, 𝓦) e₀ e₁ τ` | same |

##### Theorems of λ|2|^ref

| # | Paper Theorem / Lemma | Lean Identifier | File (TwoLevelFinal) |
|---|---|---|---|
| Theorem 6.1 | Progress | `progress` | [`SyntacticSoundness/Progress.lean`](Instar/TwoLevelFinal/SyntacticSoundness/Progress.lean) |
| Theorem 6.2 | Preservation | `preservation` | [`SyntacticSoundness/Preservation.lean`](Instar/TwoLevelFinal/SyntacticSoundness/Preservation.lean) |
| Theorem 6.3 | Syntactic Erasure Soundness | `typing.erase.safety` | [`SyntacticTyping/EraseSafety.lean`](Instar/TwoLevelFinal/SyntacticTyping/EraseSafety.lean) |
| Theorem 6.4 | Semantics Preservation | `semantics_preservation.stepn.rep` | [`SemanticsPreservation/Preservation.lean`](Instar/TwoLevelFinal/SemanticsPreservation/Preservation.lean) |

---

### 3. Key Design Choices

#### Locally Nameless Representation

Free variables use de Bruijn levels; bound variables use de Bruijn
indices. This follows Charguéraud (2012) and is chosen to simplify
fresh variable generation during let-insertion and avoid α-equivalence.

#### Level-Indexed Reduction

Because reification contexts introduce second-stage bindings, the
reduction relation is indexed by the current de Bruijn level.
Evaluation contexts track this level.

#### World Model (λ|2|^ref only)

A partial bijection on locations relates stores across two program
runs. Since stores contain only natural numbers (first-order), worlds
need not be recursively indexed.

---

### 4. Proof Structure & Organization

#### File Organization

Each calculus variant (`TwoLevelBasic`, `TwoLevelRec`, `TwoLevelMut`, `TwoLevelFinal`)
follows the same module hierarchy:

```
Instar/<Variant>/
├── Utils/
│   ├── Defs.lean          
│   └── List.lean          
├── Syntax/
│   ├── Basic.lean           — Core AST definitions (Expr, Stage, Ty)
│   ├── Defs.lean          
│   ├── Transform.lean       — Substitution, erasure, opening/closing
│   ├── Fv.lean              — Free variable computations
│   ├── LocallyNameless.lean — Local closure
│   ├── Grounded.lean      
│   ├── Identity.lean      
│   ├── Commutativity.lean 
│   └── Intro.lean         
├── OperationalSemantics/
│   ├── Value.lean           — Value predicate
│   ├── EvalCtx.lean         — Evaluation/Reification contexts (ctx𝔹, ctxℝ, ctx𝔼, ctx𝕄)
│   ├── SmallStep.lean       — Head/Single/multi-step reduction
│   ├── Defs.lean          
│   ├── Congruence.lean    
│   ├── Deterministic.lean   — Determinism theorem
│   ├── Confluence.lean    
│   ├── Refine.lean        
│   ├── Termination.lean     — Termination characterization (Rec/Final only)
│   └── Store.lean           — Store model (Mut/Final only)
├── SyntacticTyping/
│   ├── Ty.lean              — Types, well-formedness, type erasure
│   ├── Effect.lean          — Effect lattice
│   ├── Env.lean             — Typing environments, env erasure
│   ├── Typing.lean          — Typing judgments and rules
│   ├── Defs.lean          
│   ├── Weakening.lean     
│   ├── Shrinking.lean     
│   └── EraseSafety.lean     — Syntactic Erasure Soundness
├── SyntacticSoundness/
│   ├── Progress.lean        — Progress theorem
│   ├── Preservation.lean    — Preservation theorem
│   ├── Soundness.lean       — Type Soundness (progress + preservation)
│   ├── Defs.lean         
│   ├── PresvCtx.lean      
│   ├── PresvSubst.lean    
│   ├── PresvOpenSubst.lean   
│   ├── PresvPure.lean    
│   ├── PresvReflect.lean  
│   └── PresvMut.lean     
├── CtxEquiv/
│   ├── ObsCtx.lean          — Observational contexts & Contextual equivalence
│   ├── Defs.lean          
│   └── Transitivity.lean    — Transitivity of contextual equivalence
├── LogicalEquiv/
│   ├── LogicalRelation.lean — Value/Term/Environment interpretations & Logical equivalence
│   ├── Compatibility.lean   — Compatibility lemmas
│   ├── Fundamental.lean     — Fundamental theorem
│   ├── Soundness.lean       — Soundness wrt contextual equivalence
│   ├── Completeness.lean    
│   ├── Transitivity.lean    
│   ├── Defs.lean           
│   └── World.lean           — World model (Mut/Final only)
├── SemanticsPreservation/
│   ├── PresvPure.lean       — Preservation for pure steps
│   ├── PresvReflect.lean    — Preservation for let-insertion steps
│   ├── PresvCtx.lean        
│   ├── Preservation.lean    — Main semantics preservation theorems
│   └── Defs.lean            
├── Examples/                — (TwoLevelFinal only)
│   ├── Notation.lean         
│   ├── Power.lean            
│   ├── StagePower.lean       
│   ├── Reification.lean      
│   └── PhaseConsistency.lean 
└── Defs.lean                
```

---

### 5. Axioms, Assumptions & Incomplete Proofs

#### Axiom Inventory

The mechanization contains **zero `sorry` blocks** — every theorem claimed 
in the paper is fully proved. A clean `lake build` is sufficient to confirm
this: Lean 4 treats `sorry` as a compilation warning.

#### Verifying with `#print axioms`

To audit the axioms for each key theorem, add the following lines to each
variant's `Defs.lean` (e.g., `Instar/TwoLevelRec/Defs.lean`).
They can be used to audit the assumptions a theorem relies on.

```lean
#print axioms deterministic.decomposition_ctxℙ
#print axioms deterministic

#print axioms progress.strengthened
#print axioms progress
#print axioms preservation.open_subst
#print axioms preservation
#print axioms preservation.stepn
#print axioms soundness

#print axioms typing.erase.safety

#print axioms ctx_equiv.trans
#print axioms log_equiv.fundamental
#print axioms log_equiv.soundness

#print axioms semantics_preservation.lets
#print axioms semantics_preservation.reflect.head
#print axioms semantics_preservation
#print axioms semantics_preservation.stepn
#print axioms semantics_preservation.stepn.rep
```

Then rebuild with `lake build Instar.TwoLevelRec.Defs`. Each `#print axioms`
line emits output such as:

```
'semantics_preservation.stepn.rep' depends on axioms: [Quot.sound, propext, Classical.choice]
```

All of these are standard built-in axioms (such as the propositional 
extensionality) provided by Lean.

---

## Reusability

### 1. License

This artifact is released under the **MIT License** (OSI-approved). You are free
to use, modify, and redistribute the code for any purpose, including in other
open-source or proprietary projects.

### 2. Extending the Formalization

The modular structure of each calculus variant makes it straightforward to
extend the formalization with new language features.

**Recommended workflow for adding a feature**:

1. Start from the simplest variant (`TwoLevelBasic`) and extend it first.
2. Add syntax constructors to `Expr` and `Ty`.
3. Extend substitution, erasure, and free-variable computation in `Syntax/`.
4. Add reduction rules and extend evaluation contexts in `OperationalSemantics/`.
5. Add typing rules in `SyntacticTyping/Typing.lean`.
6. Prove Progress and Preservation in `SyntacticSoundness/`.
7. Extend the logical relation in `LogicalEquiv/LogicalRelation.lean`.
8. Prove Semantics Preservation in `SemanticsPreservation/`.
9. Port the feature to richer variants (`TwoLevelRec`, `TwoLevelMut`).

### 3. Documentation

- **Paper**: See the accompanying OOPSLA 2026 paper for the full formal development and proofs.
- **Theorem inventory**: See [Section 2](#2-paper-to-artifact-correspondence) for a complete mapping from every paper theorem to its Lean identifier.
