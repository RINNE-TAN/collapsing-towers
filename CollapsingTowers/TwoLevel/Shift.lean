
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.OpenClose
@[simp]
def shiftl_at (x : ℕ) (n : ℕ) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x <= y then .fvar (y + n) else .fvar y
  | .lam₁ e => .lam₁ (shiftl_at x n e)
  | .lam₂ e => .lam₂ (shiftl_at x n e)
  | .app₁ f arg => .app₁ (shiftl_at x n f) (shiftl_at x n arg)
  | .app₂ f arg => .app₂ (shiftl_at x n f) (shiftl_at x n arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ e => .lit₂ (shiftl_at x n e)
  | .plus₁ l r => .plus₁ (shiftl_at x n l) (shiftl_at x n r)
  | .plus₂ l r => .plus₂ (shiftl_at x n l) (shiftl_at x n r)
  | .code e => .code (shiftl_at x n e)
  | .reflect e => .reflect (shiftl_at x n e)
  | .lam𝕔 e => .lam𝕔 (shiftl_at x n e)
  | .lets b e => .lets (shiftl_at x n b) (shiftl_at x n e)
  | .let𝕔 b e => .let𝕔 (shiftl_at x n b) (shiftl_at x n e)
  | .loc n => .loc n

theorem shiftl_opening :
    ∀ x y e n i, x <= y -> shiftl_at x n (opening i (.fvar y) e) = opening i (.fvar (y + n)) (shiftl_at x n e) :=
  by
  intros x y e n i HLe
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . rw [HEq]; simp; omega
    . simp; rw [if_neg HEq]; rw [if_neg HEq]; rfl
  | fvar z =>
    by_cases HLe : x <= z
    . simp; rw [if_pos HLe]; rfl
    . simp; rw [if_neg HLe]; rfl
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor; apply IH₀; apply IH₁
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH =>
    simp; apply IH

theorem shiftl_open₀ : ∀ x y e n, x <= y -> shiftl_at x n (open₀ y e) = open₀ (y + n) (shiftl_at x n e) := by
  intros _ _ _ _; apply shiftl_opening

theorem shiftl_closed_at :
    ∀ x y e n, closed_at e x -> closed_at (shiftl_at y n e) (x + n) :=
  by
  intros x y e n Hclose
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases HLe : y <= z
    . simp; rw [if_pos HLe]; simp; apply Hclose
    . simp; rw [if_neg HLe]; simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH =>
    simp; apply IH; apply Hclose

theorem shiftl_id :
    ∀ x e n, closed_at e x -> shiftl_at x n e = e :=
  by
  intros x e n
  induction e with
  | bvar j => simp
  | fvar y => simp; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    intro Hclose; simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH =>
    simp; apply IH

@[simp]
def shiftr_at (x : ℕ) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x < y then .fvar (y - 1) else .fvar y
  | .lam₁ e => .lam₁ (shiftr_at x e)
  | .lam₂ e => .lam₂ (shiftr_at x e)
  | .app₁ f arg => .app₁ (shiftr_at x f) (shiftr_at x arg)
  | .app₂ f arg => .app₂ (shiftr_at x f) (shiftr_at x arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ (shiftr_at x n)
  | .plus₁ l r => .plus₁ (shiftr_at x l) (shiftr_at x r)
  | .plus₂ l r => .plus₂ (shiftr_at x l) (shiftr_at x r)
  | .code e => .code (shiftr_at x e)
  | .reflect e => .reflect (shiftr_at x e)
  | .lam𝕔 e => .lam𝕔 (shiftr_at x e)
  | .lets b e => .lets (shiftr_at x b) (shiftr_at x e)
  | .let𝕔 b e => .let𝕔 (shiftr_at x b) (shiftr_at x e)
  | .loc n => .loc n

theorem shiftr_opening :
    ∀ x y e i, x < y -> shiftr_at x (opening i (.fvar y) e) = opening i (.fvar (y - 1)) (shiftr_at x e) :=
  by
  intros x y e i HLe
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . rw [HEq]; simp; omega
    . simp; rw [if_neg HEq, if_neg HEq]; simp
  | fvar z =>
    by_cases HLe : x < z
    . simp; rw [if_pos HLe]; rfl
    . simp; rw [if_neg HLe]; rfl
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor; apply IH₀; apply IH₁
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH =>
    simp; apply IH

theorem shiftr_open₀ : ∀ x y e, x < y -> shiftr_at x (open₀ y e) = open₀ (y - 1) (shiftr_at x e) :=
  by
  intros _ _ _
  apply shiftr_opening

theorem shiftr_closed_at : ∀ x y e, y < x -> closed_at e (x + 1) -> closed_at (shiftr_at y e) x :=
  by
  intros x y e Hxy Hclose
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases Hyz : y < z
    . simp; rw [if_pos Hyz]; simp at *; omega
    . simp; rw [if_neg Hyz]; simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH =>
    simp; apply IH; apply Hclose

theorem shiftr_closed_at_id : ∀ x e, closed_at e x -> closed_at (shiftr_at x e) x :=
  by
  intros x e Hclose
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases Hxz : x < z
    . simp; rw [if_pos Hxz]; simp at *; omega
    . simp; rw [if_neg Hxz]; simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH =>
    simp; apply IH; apply Hclose

theorem shiftr_id :
    ∀ x e, closed_at e (x + 1) -> shiftr_at x e = e :=
  by
  intros x e
  induction e with
  | bvar j => simp
  | fvar y => simp; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    intro Hclose; simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH =>
    simp; apply IH
