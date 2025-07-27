import CollapsingTowers.TwoLvLBasic.Syntax.Defs
import CollapsingTowers.TwoLvLBasic.Semantic.Value

abbrev Ctx :=
  Expr → Expr

notation:max a "⟦" b "⟧" => a b

lemma ctx_comp : (f g : Ctx) → ∀ e, f (g e) = (f ∘ g) e := by simp

lemma ctx_swap : (f : Ctx) → ∀ e, f (id e) = id (f e) := by simp

inductive ctx𝔹 : Ctx → Prop where
  | appl₁ : ∀ arg, lc arg → ctx𝔹 (fun X => .app₁ X arg)
  | appr₁ : ∀ v, value v → ctx𝔹 (fun X => .app₁ v X)
  | appl₂ : ∀ arg, lc arg → ctx𝔹 (fun X => .app₂ X arg)
  | appr₂ : ∀ v, value v → ctx𝔹 (fun X => .app₂ v X)
  | lift : ctx𝔹 (fun X => .lift X)
  | lets : ∀ e, lc_at e 1 → ctx𝔹 (fun X => .lets X e)

inductive ctxℝ : ℕ → ℕ → Ctx → Prop where
  | lam𝕔 : ctxℝ 1 lvl (fun X => .lam𝕔 ({0 ↤ lvl} X))
  | lets𝕔 : ∀ b, lc b → ctxℝ 1 lvl (fun X => .lets𝕔 b ({0 ↤ lvl} X))
  | run : ctxℝ 0 lvl (fun X => .run X)

inductive ctx𝕄 : ℕ → Ctx → Prop where
  | hole : ctx𝕄 lvl id
  | cons𝔹 : ∀ B M, ctx𝔹 B → ctx𝕄 lvl M → ctx𝕄 lvl (B ∘ M)
  | consℝ : ∀ R M, ctxℝ intro lvl R → ctx𝕄 (lvl + intro) M → ctx𝕄 lvl (R ∘ M)

inductive ctx𝔼 : Ctx → Prop where
  | hole : ctx𝔼 id
  | cons𝔹 : ∀ B E, ctx𝔹 B → ctx𝔼 E → ctx𝔼 (B ∘ E)

inductive ctxℚ : ℕ → Ctx → Prop where
  | holeℝ : ∀ R, ctxℝ intro lvl R → ctxℚ lvl R
  | cons𝔹 : ∀ B Q, ctx𝔹 B → ctxℚ lvl Q → ctxℚ lvl (B ∘ Q)
  | consℝ : ∀ R Q, ctxℝ intro lvl R → ctxℚ (lvl + intro) Q → ctxℚ lvl (R ∘ Q)

inductive ctxℙ : ℕ → Ctx → Prop where
  | hole : ctxℙ lvl id
  | consℚ : ∀ Q, ctxℚ lvl Q → ctxℙ lvl Q

mutual
  inductive ctxℙ' : ℕ → Ctx → Prop where
    | hole : ctxℙ' lvl id
    | cons𝔹 : ∀ B Q, ctx𝔹 B → ctxℚ' lvl Q → ctxℙ' lvl (B ∘ Q)
    | consℝ : ∀ R P, ctxℝ intro lvl R → ctxℙ' (lvl + intro) P → ctxℙ' lvl (R ∘ P)
  inductive ctxℚ' : ℕ → Ctx → Prop where
    | cons𝔹 : ∀ B Q, ctx𝔹 B → ctxℚ' lvl Q → ctxℚ' lvl (B ∘ Q)
    | consℝ : ∀ R P, ctxℝ intro lvl R → ctxℙ' (lvl + intro) P → ctxℚ' lvl (R ∘ P)
end

lemma lc.under_ctx𝔹 : ∀ B e i, ctx𝔹 B → lc_at e i → lc_at B⟦e⟧ i :=
  by
  intros _ _ _ HB Hlc
  induction HB with
  | appl₁ _ IH
  | appl₂ _ IH
  | lets _ IH =>
    constructor; apply Hlc
    apply lc.inc; apply IH; omega
  | appr₁ _ Hvalue
  | appr₂ _ Hvalue =>
    constructor
    apply lc.inc; apply value_impl_lc
    apply Hvalue; omega
    apply Hlc
  | lift => apply Hlc

lemma lc.under_ctxℝ : ∀ R e i intro lvl, ctxℝ intro lvl R → lc_at e i → lc_at R⟦e⟧ i :=
  by
  intros _ _ _ _ _ HR Hlc
  cases HR with
  | lam𝕔 =>
    apply lc.under_closing; omega
    apply lc.inc; apply Hlc; omega
  | lets𝕔 _ Hlcb =>
    constructor
    apply lc.inc; apply Hlcb; omega
    apply lc.under_closing; omega
    apply lc.inc; apply Hlc; omega
  | run =>
    apply Hlc

lemma lc.under_ctx𝕄 : ∀ M e i lvl, ctx𝕄 lvl M → lc_at e i → lc_at M⟦e⟧ i :=
  by
  intros _ _ _ _ HM Hlc
  induction HM with
  | hole => apply Hlc
  | cons𝔹 _ _ HB _ IHlc =>
    simp; apply lc.under_ctx𝔹
    apply HB; apply IHlc
  | consℝ _ _ HR _ IHlc =>
    simp; apply lc.under_ctxℝ
    apply HR; apply IHlc

lemma lc.under_ctx𝔼 : ∀ E e i, ctx𝔼 E → lc_at e i → lc_at E⟦e⟧ i :=
  by
  intros _ _ _ HE Hlc
  induction HE with
  | hole => apply Hlc
  | cons𝔹 _ _ HB _ IHlc =>
    simp; apply lc.under_ctx𝔹
    apply HB; apply IHlc

lemma lc.under_ctxℚ : ∀ Q e i lvl, ctxℚ lvl Q → lc_at e i → lc_at Q⟦e⟧ i :=
  by
  intros _ _ _ _ HQ Hlc
  induction HQ with
  | holeℝ _ HR => apply lc.under_ctxℝ; apply HR; apply Hlc
  | cons𝔹 _ _ HB _ IHlc =>
    simp; apply lc.under_ctx𝔹
    apply HB; apply IHlc
  | consℝ _ _ HR _ IHlc =>
    simp; apply lc.under_ctxℝ
    apply HR; apply IHlc

lemma compose.ctx𝕄_ctx𝔹 :
  ∀ lvl M B,
    ctx𝕄 lvl M →
    ctx𝔹 B →
    ctx𝕄 lvl (M ∘ B) :=
  by
  intros lvl M B HM HB
  induction HM
  case hole =>
    apply ctx𝕄.cons𝔹 _ _ HB
    apply ctx𝕄.hole
  case cons𝔹 HB _ IH =>
    apply ctx𝕄.cons𝔹 _ _ HB
    apply IH
  case consℝ HR _ IH =>
    apply ctx𝕄.consℝ _ _ HR
    apply IH

lemma compose.ctx𝕄_ctx𝔼 :
  ∀ lvl M E,
    ctx𝕄 lvl M →
    ctx𝔼 E →
    ctx𝕄 lvl (M ∘ E) :=
  by
  intros lvl M E HM HE
  induction HE generalizing M
  case hole =>
    apply HM
  case cons𝔹 B E HB _ IH =>
    apply IH (M ∘ B)
    apply compose.ctx𝕄_ctx𝔹
    apply HM; apply HB

lemma rewrite.ctxℚ_ctx𝕄 :
  ∀ lvl Q,
    ctxℚ lvl Q →
    ctx𝕄 lvl Q :=
  by
  intros lvl Q HQ
  induction HQ
  case holeℝ HR =>
    apply ctx𝕄.consℝ; apply HR
    apply ctx𝕄.hole
  case consℝ HR _ IH =>
    apply ctx𝕄.consℝ; apply HR
    apply IH
  case cons𝔹 HB _ IH =>
    apply ctx𝕄.cons𝔹; apply HB
    apply IH

lemma rewrite.ctxℙ_ctx𝕄 :
  ∀ lvl P,
    ctxℙ lvl P →
    ctx𝕄 lvl P :=
  by
  intros lvl P HP
  cases HP
  case hole => apply ctx𝕄.hole
  case consℚ HQ =>
    apply rewrite.ctxℚ_ctx𝕄
    apply HQ
