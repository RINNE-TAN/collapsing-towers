
import CollapsingTowers.TwoLevel.Basic
@[simp]
def neutral (x : ℕ) : Expr -> Prop
  | .bvar _ => true
  | .fvar y => y ≠ x
  | .lam₁ e => neutral x e
  | .lam₂ e => neutral x e
  | .app₁ f arg => neutral x f ∧ neutral x arg
  | .app₂ f arg => neutral x f ∧ neutral x arg
  | .lit₁ _ => true
  | .lit₂ n => neutral x n
  | .plus₁ l r => neutral x l ∧ neutral x r
  | .plus₂ l r => neutral x l ∧ neutral x r
  | .code _ => true
  | .reflect _ => true
  | .lam𝕔 e => neutral x e
  | .lets b e => neutral x b ∧ neutral x e
  | .let𝕔 _ e => neutral x e

@[simp]
def neutral_db (i : ℕ) : Expr -> Prop
  | .bvar j => j ≠ i
  | .fvar _ => true
  | .lam₁ e => neutral_db (i + 1) e
  | .lam₂ e => neutral_db i e
  | .app₁ f arg => neutral_db i f ∧ neutral_db i arg
  | .app₂ f arg => neutral_db i f ∧ neutral_db i arg
  | .lit₁ _ => true
  | .lit₂ n => neutral_db i n
  | .plus₁ l r => neutral_db i l ∧ neutral_db i r
  | .plus₂ l r => neutral_db i l ∧ neutral_db i r
  | .code _ => true
  | .reflect _ => true
  | .lam𝕔 e => neutral_db (i + 1) e
  | .lets b e => neutral_db i b ∧ neutral_db (i + 1) e
  | .let𝕔 _ e => neutral_db (i + 1) e

@[simp]
def neutral_lc : Expr -> Prop :=
  neutral_db 0

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
  | .lam𝕔 e => neutral_lc e ∧ wf_expr e
  | .lets b e => wf_expr b ∧ wf_expr e
  | .let𝕔 b e => wf_expr b ∧ neutral_lc e ∧ wf_expr e
