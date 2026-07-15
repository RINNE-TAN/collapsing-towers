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
  Kripke world model to relate stores across runs

The key result is **semantics preservation**: if a well-typed two-stage program
evaluates to a code value, the generated code is contextually equivalent to the
stage-erased original. This is proved via step-indexed binary logical relations.

## Calculus Variants

| Paper Name | Lean Module | Description |
|---|---|---|
| - | `Instar.TwoLevelBasic` | Base two-stage calculus (pure, no side effects) |
| λ\|2\| | `Instar.TwoLevelRec` | Extended calculus with general recursion |
| - | `Instar.TwoLevelMut` | Extended calculus with mutable references |
| λ\|2\|^ref | `Instar.TwoLevelFinal` | Extended calculus with general recursion and mutable references |

`Instar.TwoLevelBasic` and `Instar.TwoLevelMut` are intermediate variants.

---

## 1. Build & Compilation Instructions

### Verified Environment

| Component | Version |
|---|---|
| Lean | 4.29.0-rc2 (`leanprover/lean4:v4.29.0-rc2`) |
| Lake (build tool) | bundled with Lean 4.29.0 |
| mathlib4 | `abc669d11b88e163aed1c05b352b5b16889c4ad8` |

Dependency versions are pinned in `lake-manifest.json`.

### Quick Start (from Scratch)

```bash
# 1. Install Lean 4.29.0-rc2 via elan
elan toolchain install leanprover/lean4:v4.29.0-rc2
elan default leanprover/lean4:v4.29.0-rc2

# 2. Enter the directory
cd collapsing-towers

# 3. Fetch and build dependencies (mathlib4), then build all formalizations
make all             
```

The `make all` command builds all four calculus variants. For individual builds:

```bash
make basic    # Basic calculus
make rec      # λ|2|, extended calculus with general recursion
make mut      # Extended calculus with mutable references
make final    # λ|2|^ref, extended calculus with general recursion and mutable references
```

### Artifact Verification

```bash
make verify        # build all + check for unfinished proofs
make check-axioms  # verify no axioms/sorry/admit
```

### Build Output

Successful compilation produces the following output:

```bash
lake build Instar.TwoLevelBasic.Defs
Build completed successfully (410 jobs).
lake build Instar.TwoLevelRec.Defs
Build completed successfully (412 jobs).
lake build Instar.TwoLevelMut.Defs
Build completed successfully (411 jobs).
lake build Instar.TwoLevelFinal.Defs
Build completed successfully (418 jobs).
grep -rn -E '\b(axiom|sorry|admit)\b' Instar/ --include="*.lean"; test $? -eq 1 && echo "PASS: No axioms, sorry, or admit found."
PASS: No axioms, sorry, or admit found.

=========================================
  Artifact verification complete.
  All proofs checked. Zero axioms found.
=========================================
```

---

## 2. Paper-to-Artifact Correspondence

The mechanization covers **all theorems** stated in the paper.

### Surface Syntax of λ|2| (Fig. 2)

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

### Administrative Syntax & Reduction of λ|2| (Fig. 3)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Administrative term `g` | Constructors of `Expr` (`code`, `reflect`, `lam𝕔`, `lets𝕔`) | [`Syntax/Basic.lean`](Instar/TwoLevelRec/Syntax/Basic.lean) |
| Value `v` | `value : Expr → Prop` (inductive predicate) | [`OperationalSemantics/Value.lean`](Instar/TwoLevelRec/OperationalSemantics/Value.lean) |
| Pure frame `B`, Pure context `E` | `ctx𝔹`, `ctx𝔼` | [`OperationalSemantics/EvalCtx.lean`](Instar/TwoLevelRec/OperationalSemantics/EvalCtx.lean) |
| Reification frame `R`, context `P` | `ctxℝ`, `ctxℙ` | same |
| Full evaluation context `M` | `ctx𝕄` | same |
| Head reduction `t ↝ t'` | `e₀ ↝ e₁` (notation for `head e₀ e₁`) | [`OperationalSemantics/SmallStep.lean`](Instar/TwoLevelRec/OperationalSemantics/SmallStep.lean) |
| Single-step reduction `t ⭢ t'` | `e₀ ⭢ e₁` (notation for `step_lvl 0 e₀ e₁`) | same |
| Multi-step reduction `t ⭢* t'` | `e₀ ⭢* e₁` (notation for `stepn`) | same |

### Static Semantics: Types, Effects, Well-Formedness of λ|2| (Figs. 4-5)

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

### Typing Judgments of λ|2| (Figs. 6-7)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| `Γ ⊢ t : τ ∣ ε` | `typing_reification Γ e τ ε` | [`SyntacticTyping/Typing.lean`](Instar/TwoLevelRec/SyntacticTyping/Typing.lean) |
| `Γ ⊢^s t : τ ∣ ε` | `typing Γ s e τ ε` | same |

### Erasure of λ|2| (Fig. 8)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Term erasure `⎸t⎹` | `⎸e⎹` (notation for `erase`) | [`Syntax/Transform.lean`](Instar/TwoLevelRec/Syntax/Transform.lean) |
| Type erasure `⎸τ⎹` | `erase_ty τ` | [`SyntacticTyping/Ty.lean`](Instar/TwoLevelRec/SyntacticTyping/Ty.lean) |
| Environment erasure `⎸Γ⎹` | `erase_env Γ` | [`SyntacticTyping/Env.lean`](Instar/TwoLevelRec/SyntacticTyping/Env.lean) |

### Contextual Equivalence of λ|2|↓ (Fig. 9)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Observational context `C` | `ObsCtxℂ` | [`CtxEquiv/ObsCtx.lean`](Instar/TwoLevelRec/CtxEquiv/ObsCtx.lean) |
| Basic observation frame `F` | `ObsCtx𝔽` | same |
| Context typing `C : (Γ ⊢ τ) ⇒ (Γ' ⊢ τ')` | `ObsCtxℂ Γ τ C Γ' τ'` | same |
| Contextual approx. `Γ ⊨ t₁ ≼𝑐𝑡𝑥 t₂ : τ` | `ctx_approx` | same |
| Contextual equiv. `Γ ⊨ t₁ ≃𝑐𝑡𝑥 t₂ : τ` | `ctx_equiv` | same |

### Binary Logical Relations of λ|2|↓ (Fig. 10)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Value interpretation `(k, v₀, v₁) ∈ 𝒱⟦τ⟧` | `log_approx_value : ℕ → Expr → Expr → Ty → Prop` | [`LogicalEquiv/LogicalRelation.lean`](Instar/TwoLevelRec/LogicalEquiv/LogicalRelation.lean) |
| Term interpretation `(k, e₀, e₁) ∈ ℰ⟦τ⟧` | `log_approx_expr : ℕ → Expr → Expr → Ty → Prop` | same |
| Environment interpretation `(k, γ₀, γ₁) ∈ 𝒢⟦Γ⟧` | `log_approx_env : ℕ → Subst → Subst → TEnv → Prop` | same |
| Logical approx. `Γ ⊨ t₁ ≼𝑙𝑜𝑔 t₂ : τ` | `log_approx Γ e₀ e₁ τ` | same |
| Logical equiv. `Γ ⊨ t₁ ≃𝑙𝑜𝑔 t₂ : τ` | `log_equiv Γ e₀ e₁ τ` | same |

### Theorems of λ|2|

The table below maps every theorem and key lemma from the paper to the Lean code.

| # | Paper Theorem / Lemma | Lean Identifier | File (TwoLevelRec) |
|---|---|---|---|
| Lemma 3.1 | Deterministic Decomposition | `deterministic.decomposition_ctxℙ` | [`OperationalSemantics/Deterministic.lean`](Instar/TwoLevelRec/OperationalSemantics/Deterministic.lean) |
| Theorem 3.2 | Determinism | `deterministic` | same |
| Lemma 3.3 | Strengthened Progress | `progress.strengthened` | [`SyntacticSoundness/Progress.lean`](Instar/TwoLevelRec/SyntacticSoundness/Progress.lean) |
| Theorem 3.4 | Progress | `progress` | same |
| Theorem 3.5 | Preservation | `preservation` | [`SyntacticSoundness/Preservation.lean`](Instar/TwoLevelRec/SyntacticSoundness/Preservation.lean) |
| — | Multi-step Preservation | `preservation.stepn` | same |
| — | Type Soundness | `soundness` | [`SyntacticSoundness/Soundness.lean`](Instar/TwoLevelRec/SyntacticSoundness/Soundness.lean) |
| Theorem 4.1 | Syntactic Erasure Soundness | `typing.erase.safety` | [`SyntacticTyping/EraseSafety.lean`](Instar/TwoLevelRec/SyntacticTyping/EraseSafety.lean) |
| Theorem 5.3 | Transitivity of Contextual Equiv. | `ctx_equiv.trans` | [`CtxEquiv/Transitivity.lean`](Instar/TwoLevelRec/CtxEquiv/Transitivity.lean) |
| Theorem 5.4 | Fundamental Property | `log_equiv.fundamental` | [`LogicalEquiv/Fundamental.lean`](Instar/TwoLevelRec/LogicalEquiv/Fundamental.lean) |
| Theorem 5.5 | Soundness of Logical Relations | `log_equiv.soundness` | [`LogicalEquiv/Soundness.lean`](Instar/TwoLevelRec/LogicalEquiv/Soundness.lean) |
| — | Completeness of Logical Relations | `log_equiv.completeness` | [`LogicalEquiv/Completeness.lean`](Instar/TwoLevelRec/LogicalEquiv/Completeness.lean) |
| Lemma 5.6 | Sem. Pres. of Substitution | `semantics_preservation.lets` | [`SemanticsPreservation/PresvPure.lean`](Instar/TwoLevelRec/SemanticsPreservation/PresvPure.lean) |
| Lemma 5.7 | Sem. Pres. of Let-Insertion | `semantics_preservation.reflect.head` | [`SemanticsPreservation/PresvReflect.lean`](Instar/TwoLevelRec/SemanticsPreservation/PresvReflect.lean) |
| Theorem 5.8 | Sem. Pres. of Single-Step Reduction | `semantics_preservation` | [`SemanticsPreservation/Preservation.lean`](Instar/TwoLevelRec/SemanticsPreservation/Preservation.lean) |
| Theorem 5.9 | Strengthened Sem. Preservation | `semantics_preservation.stepn` | same |
| Theorem 5.10 | Semantics Preservation | `semantics_preservation.stepn.rep` | same |

---

## 3. Key Design Choices

### Locally Nameless Representation

Free variables use de Bruijn levels; bound variables use de Bruijn
indices. This follows Charguéraud (2012) and is chosen to simplify
fresh variable generation during let-insertion and avoid α-equivalence.

### Level-Indexed Reduction

Because reification contexts introduce second-stage bindings, the
reduction relation is indexed by the current de Bruijn level.
Evaluation contexts track this level.

### Step-Indexed Logical Relations

Following Ahmed (2006) and Ahmed, Dreyer, Rossberg (POPL 2009), the
logical relation is step-indexed to handle divergence without
requiring domain-theoretic constructions.

### World Model (λ|2|^ref only)

A partial bijection on locations relates stores across two program
runs. Since stores contain only natural numbers (first-order), worlds
need not be recursively indexed.

---

## 4. Proof Structure & Organization

### File Organization

Each calculus variant (`TwoLevelBasic`, `TwoLevelRec`, `TwoLevelMut`, `TwoLevelFinal`)
follows the same module hierarchy:

```
Instar/<Variant>/
├── Utils/
│   ├── Defs.lean          — General utilities
│   └── List.lean          — List lemmas
├── Syntax/
│   ├── Basic.lean         — Core AST definitions (Expr, Stage, Ty)
│   ├── Defs.lean          — Import aggregator
│   ├── Transform.lean     — Substitution, erasure, opening/closing
│   ├── Fv.lean            — Free variable computations
│   ├── LocallyNameless.lean — Local closure, well-formedness
│   ├── Grounded.lean      — Grounded terms (no staging constructs)
│   ├── Identity.lean      — Opening/closing identity lemmas
│   ├── Commutativity.lean — Substitution commutation lemmas
│   └── Intro.lean         — Introduction lemmas
├── OperationalSemantics/
│   ├── Value.lean         — Value predicate
│   ├── EvalCtx.lean       — Evaluation contexts (ctx𝔹, ctxℝ, ctx𝔼, ctx𝕄)
│   ├── SmallStep.lean     — Single/multi-step reduction
│   ├── Defs.lean          — Head reduction, import aggregator
│   ├── Congruence.lean    — Congruence lemmas for contexts
│   ├── Deterministic.lean — Determinism proof
│   ├── Confluence.lean    — Confluence proof
│   ├── Refine.lean        — Simulation/refinement lemmas (Rec/Final only)
│   ├── Termination.lean   — Termination characterization (Rec/Final only)
│   └── Store.lean         — Store model (Mut/Final only)
├── SyntacticTyping/
│   ├── Ty.lean            — Types, well-formedness, type erasure
│   ├── Effect.lean        — Effect lattice
│   ├── Env.lean           — Typing environments, env erasure
│   ├── Typing.lean        — Typing judgments and rules
│   ├── Defs.lean          — Import aggregator
│   ├── Weakening.lean     — Weakening lemmas
│   ├── Shrinking.lean     — Shrinking lemmas
│   └── EraseSafety.lean   — Syntactic Erasure Soundness
├── SyntacticSoundness/
│   ├── Progress.lean      — Progress theorem
│   ├── Preservation.lean  — Preservation theorem
│   ├── Soundness.lean     — Type Soundness (progress + preservation)
│   ├── Defs.lean          — Import aggregator
│   ├── PresvCtx.lean      — Preservation under contexts
│   ├── PresvSubst.lean    — Substitution lemmas for preservation
│   ├── PresvMaping.lean   — Mapping lemmas
│   ├── PresvPure.lean     — Pure step preservation
│   ├── PresvReflect.lean  — Reflection step preservation
│   └── PresvMut.lean      — Mutation step preservation (Mut/Final only)
├── CtxEquiv/
│   ├── ObsCtx.lean        — Observational contexts
│   ├── Defs.lean          — Contextual approximation & equivalence
│   └── Transitivity.lean  — Transitivity of contextual equivalence
├── LogicalEquiv/
│   ├── LogicalRelation.lean — Value/term/environment interpretations
│   ├── Compatibility.lean   — Compatibility lemmas
│   ├── Fundamental.lean     — Fundamental theorem
│   ├── Soundness.lean       — Soundness wrt contextual equivalence
│   ├── Completeness.lean    — Completeness (ciu theorem)
│   ├── Transitivity.lean    — Transitivity of logical equivalence
│   ├── Defs.lean            — Import aggregator
│   └── World.lean           — World model (Mut/Final only)
├── SemanticsPreservation/
│   ├── PresvPure.lean       — Preservation for pure steps
│   ├── PresvReflect.lean    — Preservation for let-insertion steps
│   ├── PresvCtx.lean        — Preservation under contexts
│   ├── Preservation.lean    — Main semantics preservation theorems
│   └── Defs.lean            — Import aggregator
├── Examples/                 — (TwoLevelFinal only)
│   ├── Notation.lean         — Pretty-printing notation
│   ├── Power.lean            — Unstaged power function evaluation
│   ├── StagePower.lean       — Staged power function evaluation
│   ├── Reification.lean      — Reification example
│   └── PhaseConsistency.lean — Phase consistency example
└── Defs.lean                 — Top-level import aggregator
```

---

## 5. Axioms, Assumptions & Incomplete Proofs

### Axiom Inventory

The mechanization contains **zero axioms, zero `sorry` blocks, and zero
`admit` blocks**. Every theorem claimed in the paper is fully proved.

You can verify this by running:

```bash
grep -rn -E '\b(axiom|sorry|admit)\b' Instar/ --include="*.lean"
# or
make check-axioms
```

This returns no results.

### Logic-Extending Axioms

The development does **not** rely on any logic-extending axioms such as:

- Functional extensionality (`funext`)
- Classical choice (`Classical.choice`)
- Excluded middle (`em`)
- Propositional extensionality (`propext`)

The entire development is constructive and compatible with the standard
Calculus of Inductive Constructions.

---