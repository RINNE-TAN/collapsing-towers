# instar-mechanization

Mechanized metatheory for
**"When Do Staging Annotations Preserve Semantics? Mechanizing Typed Semantics-Preserving Multi-Stage Programming with Let-Insertion"**
(OOPSLA 2026, Jun Tan and Guannan Wei).

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
| Term `t` | `Expr` (inductive type) | `Syntax/Basic.lean` |
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
| Administrative term `g` | Constructors of `Expr` (`code`, `reflect`, `lam𝕔`, `lets𝕔`) | `Syntax/Basic.lean` |
| Value `v` | `value : Expr → Prop` (inductive predicate) | `OperationalSemantics/Value.lean` |
| Pure frame `B`, Pure context `E` | `ctx𝔹`, `ctx𝔼` | `OperationalSemantics/EvalCtx.lean` |
| Reification frame `R`, context `P` | `ctxℝ`, `ctxℙ` | same |
| Full evaluation context `M` | `ctx𝕄` | same |
| Head reduction `t ↝ t'` | `e₀ ↝ e₁` (notation for `head e₀ e₁`) | `OperationalSemantics/SmallStep.lean` |
| Single-step reduction `t ⭢ t'` | `e₀ ⭢ e₁` (notation for `step_lvl 0 e₀ e₁`) | same |
| Multi-step reduction `t ⭢* t'` | `e₀ ⭢* e₁` (notation for `stepn`) | same |

### Static Semantics: Types, Effects, Well-Formedness of λ|2| (Figs. 4-5)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Type `τ` | `Ty` (inductive type) | `SyntacticTyping/Ty.lean` |
| `nat`, `unit` | `.nat`, `.unit` | same |
| `τ₁ →^ε τ₂` | `.arrow τ₁ τ₂ ε` | same |
| `rep τ` | `.rep τ` | same |
| `frag τ` | `.fragment τ` | same |
| Effect `ε` ∈ {⊥, ⊤} | `Effect` enum (`⊥` / `⊤`) | `SyntacticTyping/Effect.lean` |
| Effect lattice ⊑, ⊔ | `Effect.le` (≤), `Effect.union` (∪) | same |
| Typing context `Γ` | `TEnv` (list of `Ty × Stage`) | `SyntacticTyping/Env.lean` |
| Well-formed type `WF^s τ` | `wbt s τ` | `SyntacticTyping/Ty.lean` |

### Typing Judgments of λ|2| (Figs. 6-7)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| `Γ ⊢ t : τ ∣ ε` | `typing_reification Γ e τ ε` | `SyntacticTyping/Typing.lean` |
| `Γ ⊢^s t : τ ∣ ε` | `typing Γ s e τ ε` | same |

### Erasure of λ|2| (Fig. 8)

| Paper Identifier | Lean Identifier | File |
|---|---|---|
| Term erasure `⎸t⎹` | `⎸e⎹` (notation for `erase`) | `Syntax/Transform.lean` |
| Type erasure `⎸τ⎹` | `erase_ty τ` | `SyntacticTyping/Ty.lean` |
| Environment erasure `⎸Γ⎹` | `erase_env Γ` | `SyntacticTyping/Env.lean` |
