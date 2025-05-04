
import Mathlib.Data.Finset.Basic
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.OpenClose
import CollapsingTowers.TwoLevel.Env
abbrev Ctx :=
  Expr -> Expr

notation:max a "⟦" b "⟧" => a b

inductive ctx𝔹 : Ctx -> Prop where
  | appl₁ : ∀ arg, lc arg -> ctx𝔹 (fun X => .app₁ X arg)
  | appr₁ : ∀ v, value v -> ctx𝔹 (fun X => .app₁ v X)
  | appl₂ : ∀ arg, lc arg -> ctx𝔹 (fun X => .app₂ X arg)
  | appr₂ : ∀ v, value v -> ctx𝔹 (fun X => .app₂ v X)
  | plusl₁ : ∀ r, lc r -> ctx𝔹 (fun X => .plus₁ X r)
  | plusr₁ : ∀ v, value v -> ctx𝔹 (fun X => .plus₁ v X)
  | plusl₂ : ∀ r, lc r -> ctx𝔹 (fun X => .plus₂ X r)
  | plusr₂ : ∀ v, value v -> ctx𝔹 (fun X => .plus₂ v X)
  | lets : ∀ e, closedb_at e 1 -> ctx𝔹 (fun X => .lets X e)

theorem lc_ctx𝔹 : ∀ B e, ctx𝔹 B -> lc e -> lc B⟦e⟧ :=
  by
  intros B e HB Hlc
  induction HB with
  | appl₁ _ IH
  | appl₂ _ IH
  | plusl₁ _ IH
  | plusl₂ _ IH
  | lets _ IH => constructor; apply Hlc; apply IH
  | appr₁ _ Hvalue
  | appr₂ _ Hvalue
  | plusr₁ _ Hvalue
  | plusr₂ _ Hvalue => constructor; apply value_lc; apply Hvalue; apply Hlc

theorem close_at𝔹 : ∀ B e₀ e₁ x, ctx𝔹 B -> closed_at B⟦e₀⟧ x -> closed_at e₁ x -> closed_at B⟦e₁⟧ x :=
  by
  intros _ _ _ _ HB He₀ He₁
  cases HB with
  | appl₁ | appl₂ | plusl₁ | plusl₂ | lets =>
    constructor; apply He₁; apply He₀.right
  | appr₁ | appr₂ | plusr₁ | plusr₂ =>
    constructor; apply He₀.left; apply He₁

theorem open_ctx𝔹_map : ∀ B e x, ctx𝔹 B -> open₀ x B⟦e⟧ = B⟦open₀ x e⟧ :=
  by
  intros B e x HB
  induction HB with
  | appl₁ _ IH
  | appl₂ _ IH
  | plusl₁ _ IH
  | plusl₂ _ IH
  | lets _ IH => simp; apply closedb_opening_id; apply IH
  | appr₁ _ Hvalue
  | appr₂ _ Hvalue
  | plusr₁ _ Hvalue
  | plusr₂ _ Hvalue => simp; apply closedb_opening_id; apply value_lc; apply Hvalue

inductive ctxℝ : ℕ -> Ctx -> Prop where
  | lam𝕔 : ∀ τ, ctxℝ lvl (fun X => .lam𝕔 τ (close₀ lvl X))
  | let𝕔 : ∀ b, lc b -> ctxℝ lvl (fun X => .let𝕔 b (close₀ lvl X))

theorem lc_ctxℝ : ∀ R e n, ctxℝ n R -> lc e -> lc R⟦e⟧ :=
  by
  intros R e n HR Hlc
  induction HR with
  | lam𝕔 =>
    apply close_closedb; omega
    apply closedb_inc; apply Hlc; omega
  | let𝕔 _ Hlcb =>
    constructor
    apply Hlcb
    apply close_closedb; omega
    apply closedb_inc; apply Hlc; omega

inductive ctx𝕄 : ℕ -> Ctx -> Prop where
  | hole : ctx𝕄 lvl id
  | cons𝔹 : ∀ B M, ctx𝔹 B -> ctx𝕄 lvl M -> ctx𝕄 lvl (B ∘ M)
  | consℝ : ∀ R M, ctxℝ lvl R -> ctx𝕄 (lvl + 1) M -> ctx𝕄 lvl (R ∘ M)

theorem lc_ctx𝕄 : ∀ M e n, ctx𝕄 n M -> lc e -> lc M⟦e⟧ :=
  by
  intros _ _ _ HM Hlc
  induction HM with
  | hole => apply Hlc
  | cons𝔹 _ _ HB _ IHlc => simp; apply lc_ctx𝔹; apply HB; apply IHlc
  | consℝ _ _ HR _ IHlc => simp; apply lc_ctxℝ; apply HR; apply IHlc

inductive ctx𝔼 : Ctx -> Prop where
  | hole : ctx𝔼 id
  | cons𝔹 : ∀ B E, ctx𝔹 B -> ctx𝔼 E -> ctx𝔼 (B ∘ E)

theorem lc_ctx𝔼 : ∀ E e, ctx𝔼 E -> lc e -> lc E⟦e⟧ :=
  by
  intros _ _ HE Hlc
  induction HE with
  | hole => apply Hlc
  | cons𝔹 _ _ HB _ IHlc => simp; apply lc_ctx𝔹; apply HB; apply IHlc

theorem close_at𝔼 : ∀ E e₀ e₁ x, ctx𝔼 E -> closed_at E⟦e₀⟧ x -> closed_at e₁ x -> closed_at E⟦e₁⟧ x :=
  by
  intros _ _ _ _ HE He₀ He₁
  induction HE with
  | hole => apply He₁
  | cons𝔹 _ _ HB _ IH =>
    simp; apply close_at𝔹; apply HB; apply He₀
    apply IH; cases HB <;> simp at He₀
    repeat
      first
      | apply He₀.left
      | apply He₀.right

theorem open_ctx𝔼_map : ∀ E e x, ctx𝔼 E -> open₀ x E⟦e⟧ = E⟦open₀ x e⟧ :=
  by
  intros _ _ _ HE
  induction HE with
  | hole => rfl
  | cons𝔹 _ _ HB _ IH =>
    simp at *; rw [← IH]
    apply open_ctx𝔹_map; apply HB

inductive ctxℙ : ℕ -> Ctx -> Prop where
  | hole : ctxℙ 0 id
  | holeℝ : ∀ R, ctxℝ lvl R -> ctxℙ lvl R
  | cons𝔹 : ∀ B P, ctx𝔹 B -> ctxℙ (lvl + 1) P -> ctxℙ (lvl + 1) (B ∘ P)
  | consℝ : ∀ R P, ctxℝ lvl R -> ctxℙ (lvl + 1) P -> ctxℙ lvl (R ∘ P)

theorem lc_ctxℙ : ∀ P e n, ctxℙ n P -> lc e -> lc P⟦e⟧ :=
  by
  intros _ _ _ HM Hlc
  induction HM with
  | hole => apply Hlc
  | holeℝ _ HR => apply lc_ctxℝ; apply HR; apply Hlc
  | cons𝔹 _ _ HB _ IHlc => simp; apply lc_ctx𝔹; apply HB; apply IHlc
  | consℝ _ _ HR _ IHlc => simp; apply lc_ctxℝ; apply HR; apply IHlc

inductive head𝕄 : Expr -> Expr -> Prop where
  | lets : ∀ e v, value v -> head𝕄 (.lets v e) (open_subst v e)
  | app₁ : ∀ e v, value v -> head𝕄 (.app₁ (.lam₁ _ e) v) (open_subst v e)
  | app₂ : ∀ f arg, head𝕄 (.app₂ (.code f) (.code arg)) (.reflect (.app₁ f arg))
  | plus₁ : ∀ l r, head𝕄 (.plus₁ (.lit₁ l) (.lit₁ r)) (.lit₁ (l + r))
  | plus₂ : ∀ l r, head𝕄 (.plus₂ (.code l) (.code r)) (.reflect (.plus₁ l r))
  | lit₂ : ∀ n, head𝕄 (.lit₂ n) (.code (.lit₁ n))
  | lam₂ : ∀ τ e, head𝕄 (.lam₂ (.rep τ) e) (.lam𝕔 τ (map𝕔₀ e))
  | lam𝕔 : ∀ τ e, head𝕄 (.lam𝕔 τ (.code e)) (.reflect (.lam₁ τ e))
  | let𝕔 : ∀ b e, head𝕄 (.let𝕔 b (.code e)) (.code (.lets b e))

inductive step : Expr -> Expr -> Prop where
  | step𝕄 : ∀ M e₀ e₁, ctx𝕄 0 M -> lc e₀ -> head𝕄 e₀ e₁ -> step M⟦e₀⟧ M⟦e₁⟧
  | reflect : ∀ P E b, ctxℙ 0 P -> ctx𝔼 E -> lc b -> step P⟦E⟦.reflect b⟧⟧ P⟦.let𝕔 b E⟦.code (.bvar 0)⟧⟧

inductive stepn : Expr → Expr → Prop
  | refl : ∀ e, stepn e e
  | multi : ∀ e₁ e₂ e₃, stepn e₁ e₂ → step e₂ e₃ → stepn e₁ e₃

/-- Examples:
lam₂ x. x +₂ (x +₂ x)
→⋆
code {
  lets f = lam₁ x.
    lets y = x + x in
    lets z = x + y in z
  in f
}
-/
def x₀ : Expr :=
  .fvar 0

def x₁ : Expr :=
  .fvar 1

def x₂ : Expr :=
  .fvar 2

def x₃ : Expr :=
  .fvar 3

def expr₀ : Expr :=
  .lam₂ (.rep .nat) (close₀ 0 (.plus₂ x₀ (.plus₂ x₀ x₀)))

def expr₁ : Expr :=
  .lam𝕔 .nat (close₀ 0 (.plus₂ (.code x₀) (.plus₂ (.code x₀) (.code x₀))))

def expr₂ : Expr :=
  .lam𝕔 .nat (close₀ 0 (.plus₂ (.code x₀) (.reflect (.plus₁ x₀ x₀))))

def expr₃ : Expr :=
  .lam𝕔 .nat (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.plus₂ (.code x₀) (.code x₁)))))

def expr₄ : Expr :=
  .lam𝕔 .nat (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.reflect (.plus₁ x₀ x₁)))))

def expr₅ : Expr :=
  .lam𝕔 .nat (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.let𝕔 (.plus₁ x₀ x₁) (close₀ 2 (.code x₂))))))

def expr₆ : Expr :=
  .lam𝕔 .nat (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.code (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))

def expr₇ : Expr :=
  .lam𝕔 .nat (close₀ 0 (.code (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))

def expr₈ : Expr :=
  .reflect (.lam₁ .nat (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))

def expr₉ : Expr :=
  .let𝕔 (.lam₁ .nat (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))
    (close₀ 3 (.code x₃))

def expr𝕩 : Expr :=
  .code
    (.lets (.lam₁ .nat (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂)))))) (close₀ 3 x₃))

example : step expr₀ expr₁ := by
  rw [expr₀]
  rw [expr₁]
  apply step.step𝕄 _ _ _ ctx𝕄.hole
  repeat constructor

example : step expr₁ expr₂ := by
  rw [expr₁]
  rw [expr₂]
  apply step.step𝕄 _ _ _ (ctx𝕄.consℝ _ _ (ctxℝ.lam𝕔 _) (ctx𝕄.cons𝔹 _ _ (ctx𝔹.plusr₂ _ _) ctx𝕄.hole))
  repeat constructor

example : step expr₂ expr₃ := by
  rw [expr₂]
  rw [expr₃]
  apply step.reflect _ _ _ (ctxℙ.holeℝ _ (ctxℝ.lam𝕔 _)) (ctx𝔼.cons𝔹 _ _ (ctx𝔹.plusr₂ _ _) ctx𝔼.hole)
  repeat constructor

example : step expr₃ expr₄ := by
  rw [expr₃]
  rw [expr₄]
  apply step.step𝕄 _ _ _ (ctx𝕄.consℝ _ _ (ctxℝ.lam𝕔 _) (ctx𝕄.consℝ _ _ (ctxℝ.let𝕔 _ _) ctx𝕄.hole))
  repeat constructor

example : step expr₄ expr₅ := by
  rw [expr₄]
  rw [expr₅]
  apply step.reflect _ _ _ (ctxℙ.consℝ _ _ (ctxℝ.lam𝕔 _) (ctxℙ.holeℝ _ (ctxℝ.let𝕔 _ _))) ctx𝔼.hole
  repeat constructor

example : step expr₅ expr₆ := by
  rw [expr₅]
  rw [expr₆]
  apply step.step𝕄 _ _ _ (ctx𝕄.consℝ _ _ (ctxℝ.lam𝕔 _) (ctx𝕄.consℝ _ _ (ctxℝ.let𝕔 _ _) ctx𝕄.hole))
  repeat constructor

example : step expr₆ expr₇ := by
  rw [expr₆]
  rw [expr₇]
  apply step.step𝕄 _ _ _ (ctx𝕄.consℝ _ _ (ctxℝ.lam𝕔 _) ctx𝕄.hole)
  repeat constructor

example : step expr₇ expr₈ := by
  rw [expr₇]
  rw [expr₈]
  rw [x₀]
  rw [x₁]
  rw [x₂]
  simp
  apply step.step𝕄 _ _ _ ctx𝕄.hole
  repeat constructor

example : step expr₈ expr₉ := by
  rw [expr₈]
  rw [expr₉]
  apply step.reflect _ _ _ ctxℙ.hole ctx𝔼.hole
  repeat constructor

example : step expr₉ expr𝕩 := by
  rw [expr₉]
  rw [expr𝕩]
  apply step.step𝕄 _ _ _ ctx𝕄.hole
  repeat constructor
