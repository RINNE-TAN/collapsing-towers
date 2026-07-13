import Instar.TwoLevelBasic.Syntax.Defs
import Instar.TwoLevelBasic.OperationalSemantics.Value

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

lemma lc.under_ctx𝔹 : ∀ B e i, ctx𝔹 B → lc_at e i → lc_at B⟦e⟧ i :=
  by
  intros _ _ _ HB Hlc
  induction HB with
  | lift => apply Hlc
  | appl₁ _ IHlc
  | appl₂ _ IHlc
  | lets _ IHlc =>
    constructor
    apply Hlc
    apply lc.inc; apply IHlc; omega
  | appr₁ _ Hvalue
  | appr₂ _ Hvalue =>
    constructor
    apply lc.inc; apply lc.value; apply Hvalue; omega
    apply Hlc

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
  | cons𝔹 _ _ HB _ IH =>
    apply lc.under_ctx𝔹 _ _ _ HB IH
  | consℝ _ _ HR _ IH =>
    apply lc.under_ctxℝ _ _ _ _ _ HR IH

lemma lc.under_ctx𝔼 : ∀ E e i, ctx𝔼 E → lc_at e i → lc_at E⟦e⟧ i :=
  by
  intros _ _ _ HE Hlc
  induction HE with
  | hole => apply Hlc
  | cons𝔹 _ _ HB _ IH =>
    apply lc.under_ctx𝔹 _ _ _ HB IH

lemma lc.under_ctxℚ : ∀ Q e i lvl, ctxℚ lvl Q → lc_at e i → lc_at Q⟦e⟧ i :=
  by
  intros _ _ _ _ HQ Hlc
  induction HQ with
  | holeℝ _ HR => apply lc.under_ctxℝ _ _ _ _ _ HR Hlc
  | cons𝔹 _ _ HB _ IH =>
    apply lc.under_ctx𝔹 _ _ _ HB IH
  | consℝ _ _ HR _ IH =>
    apply lc.under_ctxℝ _ _ _ _ _ HR IH

lemma lc.under_ctxℙ : ∀ P e i lvl, ctxℙ lvl P → lc_at e i → lc_at P⟦e⟧ i :=
  by
  intros _ _ _ _ HP Hlc
  cases HP
  case hole => apply Hlc
  case consℚ HQ =>
    apply lc.under_ctxℚ _ _ _ _ HQ Hlc

lemma closed.decompose_ctx𝔹 : ∀ B e x, ctx𝔹 B → closed_at B⟦e⟧ x → closed_at e x :=
  by
  intros B e x HB Hclosed
  cases HB with
  | appl₁| appl₂| lets => apply Hclosed.left
  | appr₁| appr₂ => apply Hclosed.right
  | lift => apply Hclosed

lemma closed.decompose_ctx𝔼 : ∀ E e₀ x, ctx𝔼 E → closed_at E⟦e₀⟧ x → closed_at e₀ x :=
  by
  intros _ _ _ HE Hclosed
  induction HE with
  | hole => apply Hclosed
  | cons𝔹 _ _ HB _ IH =>
    apply IH; apply closed.decompose_ctx𝔹
    apply HB; apply Hclosed

lemma closed.under_ctx𝔹 : ∀ B e₀ e₁ x, ctx𝔹 B → closed_at B⟦e₀⟧ x → closed_at e₁ x → closed_at B⟦e₁⟧ x :=
  by
  intros _ _ _ _ HB Hclosed₀ Hclosed₁
  cases HB with
  | appl₁| appl₂| lets =>
    constructor; apply Hclosed₁; apply Hclosed₀.right
  | appr₁| appr₂ =>
    constructor; apply Hclosed₀.left; apply Hclosed₁
  | lift => apply Hclosed₁

lemma closed.under_ctx𝔼 : ∀ E e₀ e₁ x, ctx𝔼 E → closed_at E⟦e₀⟧ x → closed_at e₁ x → closed_at E⟦e₁⟧ x :=
  by
  intros E e₀ e₁ x HE Hclosed₀ Hclosed₁
  induction HE with
  | hole => apply Hclosed₁
  | cons𝔹 _ _ HB _ IH =>
    apply closed.under_ctx𝔹 _ _ _ _ HB Hclosed₀
    apply IH; apply closed.decompose_ctx𝔹 _ _ _ HB Hclosed₀

lemma fv.under_ctx𝔹 :
  ∀ B e₀ e₁,
    ctx𝔹 B →
    fv e₁ ⊆ fv e₀ →
    fv B⟦e₁⟧ ⊆ fv B⟦e₀⟧ :=
  by
  intros B e₀ e₁ HB Hsubst
  cases HB with
  | appl₁| appl₂| lets =>
    apply Set.union_subset_union
    apply Hsubst; rfl
  | appr₁| appr₂ =>
    apply Set.union_subset_union
    rfl; apply Hsubst
  | lift => apply Hsubst

lemma fv.under_ctxℝ :
  ∀ intro lvl R e₀ e₁,
    ctxℝ intro lvl R →
    fv e₁ ⊆ fv e₀ →
    fv R⟦e₁⟧ ⊆ fv R⟦e₀⟧ :=
  by
  intros intro lvl R e₀ e₁ HR Hsubst
  cases HR with
  | lam𝕔 =>
    simp [fv.under_closing]
    rw [Set.subset_insert_iff]
    left; apply Hsubst
  | lets𝕔 =>
    simp
    rw [fv.under_closing, fv.under_closing]
    apply Set.subset_union_of_subset_right
    apply Set.diff_subset_diff_left
    apply Hsubst
  | run => apply Hsubst

lemma fv.under_ctx𝕄 :
  ∀ lvl M e₀ e₁,
    ctx𝕄 lvl M →
    fv e₁ ⊆ fv e₀ →
    fv M⟦e₁⟧ ⊆ fv M⟦e₀⟧ :=
  by
  intros lvl M e₀ e₁ HM Hsubst
  induction HM with
  | hole => apply Hsubst
  | cons𝔹 _ _ HB _ IH =>
    apply fv.under_ctx𝔹 _ _ _ HB IH
  | consℝ _ _ HR _ IH =>
    apply fv.under_ctxℝ _ _ _ _ _ HR IH

lemma fv.under_ctx𝔼 :
  ∀ E e₀ e₁,
    ctx𝔼 E →
    fv e₁ ⊆ fv e₀ →
    fv E⟦e₁⟧ ⊆ fv E⟦e₀⟧ :=
  by
  intros E e₀ e₁ HE Hsubst
  induction HE with
  | hole => apply Hsubst
  | cons𝔹 _ _ HB _ IH =>
    apply fv.under_ctx𝔹 _ _ _ HB IH

lemma fv.under_ctxℚ :
  ∀ lvl Q e₀ e₁,
    ctxℚ lvl Q →
    fv e₁ ⊆ fv e₀ →
    fv Q⟦e₁⟧ ⊆ fv Q⟦e₀⟧ :=
  by
  intros lvl Q e₀ e₁ HQ Hsubst
  induction HQ with
  | holeℝ _ HR =>
    apply fv.under_ctxℝ _ _ _ _ _ HR Hsubst
  | cons𝔹 _ _ HB _ IH =>
    apply fv.under_ctx𝔹 _ _ _ HB IH
  | consℝ _ _ HR _ IH =>
    apply fv.under_ctxℝ _ _ _ _ _ HR IH

lemma fv.decompose_ctx𝔹 : ∀ B e, ctx𝔹 B → fv e ⊆ fv B⟦e⟧ :=
  by
  intros _ _ HB
  cases HB <;> simp

lemma fv.decompose_ctx𝔼 : ∀ E e, ctx𝔼 E → fv e ⊆ fv E⟦e⟧ :=
  by
  intros _ _ HE
  induction HE with
  | hole => rfl
  | cons𝔹 _ _ HB _ IH =>
    apply Set.Subset.trans; apply IH
    apply fv.decompose_ctx𝔹; apply HB

lemma opening.under_ctx𝔹 : ∀ B e i x, ctx𝔹 B → opening i x B⟦e⟧ = B⟦opening i x e⟧ :=
  by
  intros B e i x HB
  cases HB with
  | appl₁ _ IH
  | appl₂ _ IH
  | lets _ IH =>
    simp
    apply identity.opening
    apply lc.inc; apply IH; omega
  | appr₁ _ Hvalue
  | appr₂ _ Hvalue =>
    simp
    apply identity.opening
    apply lc.inc; apply lc.value; apply Hvalue; omega
  | lift => simp

lemma opening.under_ctx𝔼 : ∀ E e i x, ctx𝔼 E → opening i x E⟦e⟧ = E⟦opening i x e⟧ :=
  by
  intros _ _ _ _ HE
  induction HE with
  | hole => rfl
  | cons𝔹 _ _ HB _ IH =>
    simp [← IH]; apply opening.under_ctx𝔹; apply HB

lemma erase.under_ctx𝔹 :
  ∀ B e,
    ctx𝔹 B →
    ⎸B⟦⎸e⎹⟧⎹ = ⎸B⟦e⟧⎹ :=
  by
  intros B e HB
  cases HB
  all_goals
    simp [← grounded_iff_erase_identity]
    apply grounded.under_erase

lemma erase.under_ctx𝔼 :
  ∀ E e,
    ctx𝔼 E →
    ⎸E⟦⎸e⎹⟧⎹ = ⎸E⟦e⟧⎹ :=
  by
  intros E e HE
  induction HE generalizing e
  case hole =>
    simp [← grounded_iff_erase_identity]
    apply grounded.under_erase
  case cons𝔹 B E HB HE IH =>
    simp; rw [← erase.under_ctx𝔹 _ _ HB, IH, erase.under_ctx𝔹 _ _ HB]

lemma subst.under_ctx𝔹 : ∀ B e₀ e₁ v x, ctx𝔹 B → closed_at B⟦e₀⟧ x → subst x v B⟦e₁⟧ = B⟦subst x v e₁⟧ :=
  by
  intros _ _ _ _ _ HB Hclosed
  cases HB with
  | appl₁| appl₂| lets =>
    simp; apply identity.subst; apply Hclosed.right
  | appr₁| appr₂ =>
    simp; apply identity.subst; apply Hclosed.left
  | lift => simp

lemma subst.under_ctx𝔼 : ∀ E e₀ e₁ v x, ctx𝔼 E → closed_at E⟦e₀⟧ x → subst x v E⟦e₁⟧ = E⟦subst x v e₁⟧ :=
  by
  intros _ _ _ _ _ HE Hclosed
  induction HE with
  | hole => simp
  | cons𝔹 _ E HB _ IH =>
    simp; rw [← IH]
    apply subst.under_ctx𝔹 _ _ _ _ _ HB Hclosed
    apply closed.decompose_ctx𝔹 _ _ _ HB Hclosed

lemma grounded.decompose_ctx𝔹 : ∀ B e, ctx𝔹 B → grounded B⟦e⟧ → grounded e :=
  by
  intros B e HB HG
  cases HB with
  | appl₁| lets => apply HG.left
  | appr₁ => apply HG.right
  | appl₂| appr₂| lift => nomatch HG

lemma grounded.decompose_ctxℝ : ∀ intro lvl R e, ctxℝ intro lvl R → ¬grounded R⟦e⟧ :=
  by
  intros intro lvl R e HR HG
  cases HR <;> nomatch HG

lemma grounded.decompose_ctx𝕄 : ∀ lvl M e, ctx𝕄 lvl M → grounded M⟦e⟧ → grounded e :=
  by
  intros lvl M e HM HG
  induction HM
  case hole => apply HG
  case cons𝔹 HB _ IH =>
    apply IH; apply grounded.decompose_ctx𝔹 _ _ HB HG
  case consℝ HR _ IH =>
    exfalso; apply grounded.decompose_ctxℝ _ _ _ _ HR HG

lemma grounded.decompose_ctx𝔼 : ∀ E e, ctx𝔼 E → grounded E⟦e⟧ → grounded e :=
  by
  intros E e HE HG
  induction HE
  case hole => apply HG
  case cons𝔹 HB _ IH =>
    apply IH; apply grounded.decompose_ctx𝔹 _ _ HB HG

lemma grounded.under_ctx𝔹 : ∀ B e₀ e₁, ctx𝔹 B → grounded B⟦e₀⟧ → grounded e₁ → grounded B⟦e₁⟧ :=
  by
  intros B e₀ e₁ HB HG₀ HG₁
  cases HB with
  | appl₁| lets =>
    constructor; apply HG₁; apply HG₀.right
  | appr₁ =>
    constructor; apply HG₀.left; apply HG₁
  | appl₂| appr₂| lift =>
    nomatch HG₀

lemma grounded.under_ctx𝔼 : ∀ E e₀ e₁, ctx𝔼 E → grounded E⟦e₀⟧ → grounded e₁ → grounded E⟦e₁⟧ :=
  by
  intros E e₀ e₁ HE HG₀ HG₁
  induction HE
  case hole => apply HG₁
  case cons𝔹 B M HB _ IH =>
    apply grounded.under_ctx𝔹 _ _ _ HB HG₀
    apply IH; apply grounded.decompose_ctx𝔹 _ _ HB HG₀

lemma grounded.under_ctx𝕄 : ∀ lvl M e₀ e₁, ctx𝕄 lvl M → grounded M⟦e₀⟧ → grounded e₁ → grounded M⟦e₁⟧ :=
  by
  intros lvl M e₀ e₁ HM HG₀ HG₁
  induction HM
  case hole => apply HG₁
  case cons𝔹 B M HB _ IH =>
    apply grounded.under_ctx𝔹 _ _ _ HB HG₀
    apply IH; apply grounded.decompose_ctx𝔹 _ _ HB HG₀
  case consℝ HR _ IH =>
    exfalso; apply grounded.decompose_ctxℝ _ _ _ _ HR HG₀

lemma compose.ctx𝔼_ctx𝔹 :
  ∀ E B,
    ctx𝔼 E →
    ctx𝔹 B →
    ctx𝔼 (E ∘ B) :=
  by
  intros E B HE HB
  induction HE
  case hole =>
    apply ctx𝔼.cons𝔹 _ _ HB ctx𝔼.hole
  case cons𝔹 HB _ IH =>
    apply ctx𝔼.cons𝔹 _ _ HB IH

lemma compose.ctx𝕄_ctx𝔹 :
  ∀ lvl M B,
    ctx𝕄 lvl M →
    ctx𝔹 B →
    ctx𝕄 lvl (M ∘ B) :=
  by
  intros lvl M B HM HB
  induction HM
  case hole =>
    apply ctx𝕄.cons𝔹 _ _ HB ctx𝕄.hole
  case cons𝔹 HB _ IH =>
    apply ctx𝕄.cons𝔹 _ _ HB IH
  case consℝ HR _ IH =>
    apply ctx𝕄.consℝ _ _ HR IH

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
    apply compose.ctx𝕄_ctx𝔹 _ _ _ HM HB

lemma compose.ctx𝔼_ctx𝕄 :
  ∀ lvl M E,
    ctx𝕄 lvl M →
    ctx𝔼 E →
    ctx𝕄 lvl (E ∘ M) :=
  by
  intros lvl M E HM HE
  induction HE generalizing M
  case hole => apply HM
  case cons𝔹 B E HB _ IH =>
    apply ctx𝕄.cons𝔹 _ _ HB
    apply IH; apply HM

lemma rewrite.ctxℚ_ctx𝕄 :
  ∀ lvl Q,
    ctxℚ lvl Q →
    ctx𝕄 lvl Q :=
  by
  intros lvl Q HQ
  induction HQ
  case holeℝ HR =>
    apply ctx𝕄.consℝ _ _ HR ctx𝕄.hole
  case consℝ HR _ IH =>
    apply ctx𝕄.consℝ _ _ HR IH
  case cons𝔹 HB _ IH =>
    apply ctx𝕄.cons𝔹 _ _ HB IH

lemma rewrite.ctxℙ_ctx𝕄 :
  ∀ lvl P,
    ctxℙ lvl P →
    ctx𝕄 lvl P :=
  by
  intros lvl P HP
  cases HP
  case hole => apply ctx𝕄.hole
  case consℚ HQ =>
    apply rewrite.ctxℚ_ctx𝕄 _ _ HQ
