
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.OpenClose
@[simp]
def neutral (x : ℕ) : Expr -> Prop
  | .bvar _ => true
  | .fvar _ => false
  | .lam₁ e => neutral x e
  | .lam₂ e => neutral x e
  | .app₁ f arg => neutral x f ∧ neutral x arg
  | .app₂ f arg => neutral x f ∧ neutral x arg
  | .lit₁ _ => true
  | .lit₂ n => neutral x n
  | .plus₁ l r => neutral x l ∧ neutral x r
  | .plus₂ l r => neutral x l ∧ neutral x r
  | .code e => closed_at e x
  | .reflect e => closed_at e x
  | .lam𝕔 e => neutral x e
  | .lets b e => neutral x b ∧ neutral x e
  | .let𝕔 b e => closed_at b x ∧ neutral x e

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

theorem closed_at_neutral : ∀ e, closed_at e 0 -> neutral 0 e :=
  by
  intros e Hclose
  induction e with
  | bvar| lit₁ => simp
  | code| reflect => apply Hclose
  | fvar => nomatch Hclose
  | lam₁ _ IH
  | lam₂ _ IH
  | lit₂ _ IH
  | lam𝕔 _ IH => simp at *; apply IH; apply Hclose
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lets _ _ IHb IHe =>
    simp; constructor
    apply IHb; apply Hclose.left
    apply IHe; apply Hclose.right
  | let𝕔 _ _ _ IHe =>
    simp; constructor
    apply Hclose.left
    apply IHe; apply Hclose.right
