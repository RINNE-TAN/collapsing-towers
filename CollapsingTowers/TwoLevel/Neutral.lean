
import CollapsingTowers.TwoLevel.Basic
@[simp]
def neutral (i : ℕ) : Expr -> Prop
  | .bvar j => j ≠ i
  | .fvar _ => true
  | .lam₁ e => neutral (i + 1) e
  | .lam₂ e => neutral i e
  | .app₁ f arg => neutral i f ∧ neutral i arg
  | .app₂ f arg => neutral i f ∧ neutral i arg
  | .lit₁ _ => true
  | .lit₂ n => neutral i n
  | .plus₁ l r => neutral i l ∧ neutral i r
  | .plus₂ l r => neutral i l ∧ neutral i r
  | .code _ => true
  | .reflect _ => true
  | .lam𝕔 e => neutral (i + 1) e
  | .lets b e => neutral i b ∧ neutral (i + 1) e
  | .let𝕔 _ e => neutral (i + 1) e

@[simp]
def neutral₀ : Expr -> Prop :=
  neutral 0

@[simp]
def wf_expr : Expr -> Prop
  | .bvar _ => true
  | .fvar _ => true
  | .lam₁ e => wf_expr e
  | .lam₂ e => wf_expr e
  | .app₁ f arg => wf_expr f ∧ wf_expr arg
  | .app₂ f arg => wf_expr f ∧ wf_expr arg
  | .lit₁ _ => true
  | .lit₂ n => wf_expr n
  | .plus₁ l r => wf_expr l ∧ wf_expr r
  | .plus₂ l r => wf_expr l ∧ wf_expr r
  | .code e => wf_expr e
  | .reflect e => wf_expr e
  | .lam𝕔 e => neutral₀ e ∧ wf_expr e
  | .lets b e => wf_expr b ∧ wf_expr e
  | .let𝕔 b e => wf_expr b ∧ neutral₀ e ∧ wf_expr e
