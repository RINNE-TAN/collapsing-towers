
import CollapsingTowers.TwoLevelPCP.Syntax
import CollapsingTowers.TwoLevelPCP.OpenClose
abbrev Ctx :=
  Expr → Expr

notation:max a "⟦" b "⟧" => a b

inductive value : Expr → Prop where
  | lam₁ : ∀ e, lc (.lam₁ e) → value (.lam₁ e)
  | lit₁ : ∀ n, value (.lit₁ n)
  | code : ∀ e, lc e → value (.code e)

inductive ctx𝔹 : Ctx → Prop where
  | appl₁ : ∀ arg, lc arg → ctx𝔹 (fun X => .app₁ X arg)
  | appr₁ : ∀ v, value v → ctx𝔹 (fun X => .app₁ v X)
  | appl₂ : ∀ arg, lc arg → ctx𝔹 (fun X => .app₂ X arg)
  | appr₂ : ∀ v, value v → ctx𝔹 (fun X => .app₂ v X)
  | plusl₁ : ∀ r, lc r → ctx𝔹 (fun X => .plus₁ X r)
  | plusr₁ : ∀ v, value v → ctx𝔹 (fun X => .plus₁ v X)
  | plusl₂ : ∀ r, lc r → ctx𝔹 (fun X => .plus₂ X r)
  | plusr₂ : ∀ v, value v → ctx𝔹 (fun X => .plus₂ v X)
  | lift : ctx𝔹 (fun X => .lift X)
  | lets : ∀ e, closedb_at e 1 → ctx𝔹 (fun X => .lets X e)

inductive ctxℝ : ℕ → Ctx → Prop where
  | lam𝕔 : ctxℝ lvl (fun X => .lam𝕔 (close₀ lvl X))
  | let𝕔 : ∀ b, lc b → ctxℝ lvl (fun X => .let𝕔 b (close₀ lvl X))

inductive ctx𝕄 : ℕ → Ctx → Prop where
  | hole : ctx𝕄 lvl id
  | cons𝔹 : ∀ B M, ctx𝔹 B → ctx𝕄 lvl M → ctx𝕄 lvl (B ∘ M)
  | consℝ : ∀ R M, ctxℝ lvl R → ctx𝕄 (lvl + 1) M → ctx𝕄 lvl (R ∘ M)

inductive ctx𝔼 : Ctx → Prop where
  | hole : ctx𝔼 id
  | cons𝔹 : ∀ B E, ctx𝔹 B → ctx𝔼 E → ctx𝔼 (B ∘ E)

inductive ctxℚ : ℕ → Ctx → Prop where
  | holeℝ : ∀ R, ctxℝ lvl R → ctxℚ lvl R
  | cons𝔹 : ∀ B Q, ctx𝔹 B → ctxℚ lvl Q → ctxℚ lvl (B ∘ Q)
  | consℝ : ∀ R Q, ctxℝ lvl R → ctxℚ (lvl + 1) Q → ctxℚ lvl (R ∘ Q)

inductive ctxℙ : ℕ → Ctx → Prop where
  | hole : ctxℙ 0 id
  | consℚ : ∀ Q, ctxℚ lvl Q → ctxℙ lvl Q

theorem value_lc : ∀ e, value e -> lc e := by
  intro e Hvalue
  cases Hvalue with
  | lam₁ _ Hclose => apply Hclose
  | lit₁ => constructor
  | code _ Hclose => apply Hclose

-- properties of 𝔹 contexts

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
  | lift => apply Hlc

-- properties of ℝ contexts

theorem lc_ctxℝ : ∀ R e lvl, ctxℝ lvl R -> lc e -> lc R⟦e⟧ :=
  by
  intros _ _ _ HR Hlc
  induction HR with
  | lam𝕔 =>
    apply close_closedb; omega
    apply closedb_inc; apply Hlc; omega
  | let𝕔 _ Hlcb =>
    constructor
    apply Hlcb
    apply close_closedb; omega
    apply closedb_inc; apply Hlc; omega

-- properties of 𝕄 contexts

theorem lc_ctx𝕄 : ∀ M e lvl, ctx𝕄 lvl M -> lc e -> lc M⟦e⟧ :=
  by
  intros _ _ _ HM Hlc
  induction HM with
  | hole => apply Hlc
  | cons𝔹 _ _ HB _ IHlc => simp; apply lc_ctx𝔹; apply HB; apply IHlc
  | consℝ _ _ HR _ IHlc => simp; apply lc_ctxℝ; apply HR; apply IHlc

-- properties of 𝔼 contexts

theorem lc_ctx𝔼 : ∀ E e, ctx𝔼 E -> lc e -> lc E⟦e⟧ :=
  by
  intros _ _ HE Hlc
  induction HE with
  | hole => apply Hlc
  | cons𝔹 _ _ HB _ IHlc => simp; apply lc_ctx𝔹; apply HB; apply IHlc

-- properties of ℚ contexts

theorem lc_ctxℚ : ∀ Q e lvl, ctxℚ lvl Q -> lc e -> lc Q⟦e⟧ :=
  by
  intros _ _ _ HQ Hlc
  induction HQ with
  | holeℝ _ HR => apply lc_ctxℝ; apply HR; apply Hlc
  | cons𝔹 _ _ HB _ IHlc => simp; apply lc_ctx𝔹; apply HB; apply IHlc
  | consℝ _ _ HR _ IHlc => simp; apply lc_ctxℝ; apply HR; apply IHlc

inductive head𝕄 : Expr → Expr → Prop where
  | lets : ∀ e v, value v → head𝕄 (.lets v e) (open_subst v e)
  | app₁ : ∀ e v, value v → head𝕄 (.app₁ (.lam₁ e) v) (open_subst v e)
  | app₂ : ∀ f arg, head𝕄 (.app₂ (.code f) (.code arg)) (.reflect (.app₁ f arg))
  | plus₁ : ∀ l r, head𝕄 (.plus₁ (.lit₁ l) (.lit₁ r)) (.lit₁ (l + r))
  | plus₂ : ∀ l r, head𝕄 (.plus₂ (.code l) (.code r)) (.reflect (.plus₁ l r))
  | lift_lit : ∀ n, head𝕄 (.lift (.lit₁ n)) (.reflect (.lit₁ n))
  | lift_lam : ∀ e, head𝕄 (.lift (.lam₁ e)) (.lam𝕔 (map𝕔₀ e))
  | lam𝕔 : ∀ e, head𝕄 (.lam𝕔 (.code e)) (.reflect (.lam₁ e))
  | let𝕔 : ∀ b e, head𝕄 (.let𝕔 b (.code e)) (.code (.lets b e))

inductive step_lvl (lvl : ℕ) : Expr → Expr → Prop where
  | step𝕄 : ∀ M e₀ e₁, ctx𝕄 lvl M → lc e₀ → head𝕄 e₀ e₁ → step_lvl lvl M⟦e₀⟧ M⟦e₁⟧
  | reflect : ∀ P E b, ctxℙ lvl P → ctx𝔼 E → lc b → step_lvl lvl P⟦E⟦.reflect b⟧⟧ P⟦.let𝕔 b E⟦.code (.bvar 0)⟧⟧

@[simp]
def step : Expr → Expr → Prop :=
  step_lvl 0
