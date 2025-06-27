
import CollapsingTowers.TwoLevelPCP.Syntax
import CollapsingTowers.TwoLevelPCP.Store
import CollapsingTowers.TwoLevelPCP.OpenClose
import CollapsingTowers.TwoLevelPCP.Env
abbrev Ctx :=
  Expr → Expr

theorem ctx_comp : (f g : Ctx) → ∀ e, f (g e) = (f ∘ g) e := by simp

theorem ctx_swap : (f : Ctx) → ∀ e, f (id e) = id (f e) := by simp

notation:max a "⟦" b "⟧" => a b

inductive value : Expr → Prop where
  | lam : ∀ e, lc (.lam e) → value (.lam e)
  | lit : ∀ n, value (.lit n)
  | unit : value .unit
  | code : ∀ e, lc e → value (.code e)
  | loc : ∀ l, value (.loc l)

inductive ctx𝔹 : Ctx → Prop where
  | appl₁ : ∀ arg, lc arg → ctx𝔹 (fun X => .app₁ X arg)
  | appr₁ : ∀ v, value v → ctx𝔹 (fun X => .app₁ v X)
  | appl₂ : ∀ arg, lc arg → ctx𝔹 (fun X => .app₂ X arg)
  | appr₂ : ∀ v, value v → ctx𝔹 (fun X => .app₂ v X)
  | binaryl₁ : ∀ op r, lc r → ctx𝔹 (fun X => .binary₁ op X r)
  | binaryr₁ : ∀ op v, value v → ctx𝔹 (fun X => .binary₁ op v X)
  | binaryl₂ : ∀ op r, lc r → ctx𝔹 (fun X => .binary₂ op X r)
  | binaryr₂ : ∀ op v, value v → ctx𝔹 (fun X => .binary₂ op v X)
  | lift : ctx𝔹 (fun X => .lift X)
  | lets : ∀ e, closedb_at e 1 → ctx𝔹 (fun X => .lets X e)
  | load₁ : ctx𝔹 (fun X => .load₁ X)
  | alloc₁ : ctx𝔹 (fun X => .alloc₁ X)
  | storel₁ : ∀ r, lc r → ctx𝔹 (fun X => .store₁ X r)
  | storer₁ : ∀ v, value v → ctx𝔹 (fun X => .store₁ v X)
  | load₂ : ctx𝔹 (fun X => .load₂ X)
  | alloc₂ : ctx𝔹 (fun X => .alloc₂ X)
  | storel₂ : ∀ r, lc r → ctx𝔹 (fun X => .store₂ X r)
  | storer₂ : ∀ v, value v → ctx𝔹 (fun X => .store₂ v X)
  | ifz₁ : ∀ l r, lc l → lc r → ctx𝔹 (fun X => .ifz₁ X l r)
  | ifz₂ : ∀ l r, lc l → lc r → ctx𝔹 (fun X => .ifz₂ X l r)
  | fix₁ : ctx𝔹 (fun X => .fix₁ X)
  | fix₂ : ctx𝔹 (fun X => .fix₂ X)

inductive ctxℝ : ℕ → ℕ → Ctx → Prop where
  | lam𝕔 : ctxℝ 1 lvl (fun X => .lam𝕔 (close₀ lvl X))
  | let𝕔 : ∀ b, lc b → ctxℝ 1 lvl (fun X => .let𝕔 b (close₀ lvl X))
  | run : ctxℝ 0 lvl (fun X => .run X)
  | ifzl₂ : ∀ v r, value v → lc r → ctxℝ 0 lvl (fun X => .ifz₂ v X r)
  | ifzr₂ : ∀ v₀ v₁, value v₀ → value v₁ → ctxℝ 0 lvl (fun X => .ifz₂ v₀ v₁ X)

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

theorem ctxℙ_iff_ctxℙ' : ∀ P lvl, ctxℙ' lvl P ↔ ctxℙ lvl P :=
  by
  intros C lvl
  constructor
  . intro HP
    apply
      @ctxℙ'.rec
        (fun lvl P (H : ctxℙ' lvl P) => ctxℙ lvl P)
        (fun lvl P (H : ctxℚ' lvl P) => ctxℚ lvl P)
    case hole => apply ctxℙ.hole
    case cons𝔹 =>
      intros _ _ _ HB _ IHQ
      apply ctxℙ.consℚ
      apply ctxℚ.cons𝔹
      apply HB; apply IHQ
    case consℝ =>
      intros _ _ _ _ HR _ IHP
      apply ctxℙ.consℚ
      cases IHP with
      | hole =>
        apply ctxℚ.holeℝ
        apply HR
      | consℚ _ HQ =>
        apply ctxℚ.consℝ
        apply HR; apply HQ
    case cons𝔹 =>
      intros _ _ _ HB _ IHQ
      apply ctxℚ.cons𝔹
      apply HB; apply IHQ
    case consℝ =>
      intros _ _ _ _ HR _ IHP
      cases IHP with
      | hole =>
        apply ctxℚ.holeℝ
        apply HR
      | consℚ _ HQ =>
        apply ctxℚ.consℝ
        apply HR; apply HQ
    apply HP
  . intro HP
    cases HP
    case hole =>
      apply ctxℙ'.hole
    case consℚ HQ =>
      have H :
        (∃ B Q, ctx𝔹 B ∧ ctxℚ' lvl Q ∧ C = B ∘ Q) ∨
        (∃ R P intro, ctxℝ intro lvl R ∧ ctxℙ' (lvl + intro) P ∧ C = R ∘ P) :=
        by
        induction HQ with
        | holeℝ R HR =>
          right
          exists R, id
          constructor; constructor
          apply HR; constructor
          apply ctxℙ'.hole; rfl
        | cons𝔹 B₀ Q₀ HB₀ _ IHQ =>
          left; exists B₀, Q₀
          cases IHQ
          case inl IHQ =>
            have ⟨B₁, Q₁, HB₁, HQ₁, HEqC⟩ := IHQ; constructor
            apply HB₀; constructor
            rw [HEqC]; apply ctxℚ'.cons𝔹
            apply HB₁; apply HQ₁; rfl
          case inr IHQ =>
            have ⟨R, P, _, HR, HP, HEqC⟩ := IHQ; constructor
            apply HB₀; constructor
            rw [HEqC]; apply ctxℚ'.consℝ
            apply HR; apply HP; rfl
        | consℝ R₀ P₀ HR₀ _ IHP =>
          right; exists R₀, P₀
          cases IHP
          case inl IHP =>
            have ⟨B, Q, HB, HQ, HEqC⟩ := IHP
            constructor; constructor
            apply HR₀; constructor
            rw [HEqC]; apply ctxℙ'.cons𝔹
            apply HB; apply HQ; rfl
          case inr IHQ =>
            have ⟨R₁, P₁, _, HR₁, HP₁, HEqC⟩ := IHQ
            constructor; constructor
            apply HR₀; constructor
            rw [HEqC]; apply ctxℙ'.consℝ
            apply HR₁; apply HP₁; rfl
      cases H
      case inl H =>
        have ⟨B, Q, HB, HQ, HEqC⟩ := H
        rw [HEqC]; apply ctxℙ'.cons𝔹
        apply HB; apply HQ
      case inr H =>
        have ⟨R, P, _, HR, HP, HEqC⟩ := H
        rw [HEqC]; apply ctxℙ'.consℝ
        apply HR; apply HP

theorem value_lc : ∀ e, value e → lc e := by
  intro e Hvalue
  cases Hvalue with
  | lam _ Hclose => apply Hclose
  | lit => constructor
  | unit => constructor
  | code _ Hclose => apply Hclose
  | loc => constructor

-- properties of 𝔹 contexts

theorem lc_ctx𝔹 : ∀ B e n, ctx𝔹 B → closedb_at e n → closedb_at B⟦e⟧ n :=
  by
  intros _ _ _ HB Hlc
  induction HB with
  | appl₁ _ IH
  | appl₂ _ IH
  | binaryl₁ _ _ IH
  | binaryl₂ _ _ IH
  | lets _ IH
  | storel₁ _ IH
  | storel₂ _ IH =>
    constructor; apply Hlc
    apply closedb_inc; apply IH; omega
  | appr₁ _ Hvalue
  | appr₂ _ Hvalue
  | binaryr₁ _ _ Hvalue
  | binaryr₂ _ _ Hvalue
  | storer₁ _ Hvalue
  | storer₂ _ Hvalue =>
    constructor
    apply closedb_inc; apply value_lc; apply Hvalue; omega
    apply Hlc
  | lift| load₁| alloc₁| load₂| alloc₂| fix₁| fix₂ => apply Hlc
  | ifz₁ _ _ IH₀ IH₁
  | ifz₂ _ _ IH₀ IH₁ =>
    constructor; apply Hlc
    constructor
    apply closedb_inc; apply IH₀; omega
    apply closedb_inc; apply IH₁; omega

theorem closed_at_decompose𝔹 : ∀ B e₀ x, ctx𝔹 B → closed_at B⟦e₀⟧ x → closed_at e₀ x :=
  by
  intros _ _ _ HB Hclose
  cases HB with
  | appl₁| appl₂| binaryl₁| binaryl₂| lets| storel₁| storel₂ =>
    apply Hclose.left
  | appr₁| appr₂| binaryr₁| binaryr₂| storer₁| storer₂ =>
    apply Hclose.right
  | lift| load₁| alloc₁| load₂| alloc₂| fix₁| fix₂ => apply Hclose
  | ifz₁| ifz₂ => apply Hclose.left

theorem closed_at𝔹 : ∀ B e₀ e₁ x, ctx𝔹 B → closed_at B⟦e₀⟧ x → closed_at e₁ x → closed_at B⟦e₁⟧ x :=
  by
  intros _ _ _ _ HB He₀ He₁
  cases HB with
  | appl₁| appl₂| binaryl₁| binaryl₂| lets| storel₁| storel₂ =>
    constructor; apply He₁; apply He₀.right
  | appr₁| appr₂| binaryr₁| binaryr₂| storer₁| storer₂ =>
    constructor; apply He₀.left; apply He₁
  | lift| load₁| alloc₁| load₂| alloc₂| fix₁| fix₂ => apply He₁
  | ifz₁| ifz₂ => constructor; apply He₁; apply He₀.right

theorem fv_at𝔹 :
  ∀ B e₀ e₁,
    ctx𝔹 B →
    fv e₁ ⊆ fv e₀ →
    fv B⟦e₁⟧ ⊆ fv B⟦e₀⟧ :=
  by
  intros B e₀ e₁ HB Hsubst
  cases HB with
  | appl₁| appl₂| binaryl₁| binaryl₂| lets| storel₁| storel₂ =>
    apply Set.union_subset_union
    apply Hsubst; rfl
  | appr₁| appr₂| binaryr₁| binaryr₂| storer₁| storer₂ =>
    apply Set.union_subset_union
    rfl; apply Hsubst
  | lift| load₁| alloc₁| load₂| alloc₂| fix₁| fix₂ => apply Hsubst
  | ifz₁| ifz₂ =>
    apply Set.union_subset_union
    apply Set.union_subset_union
    apply Hsubst; rfl; rfl

theorem fv_decompose𝔹 : ∀ B e, ctx𝔹 B → fv e ⊆ fv B⟦e⟧ :=
  by
  intros _ _ HB
  cases HB <;> simp
  case ifz₁| ifz₂ =>
    rw [Set.union_assoc]; simp

theorem open_ctx𝔹_map : ∀ B e x, ctx𝔹 B → open₀ x B⟦e⟧ = B⟦open₀ x e⟧ :=
  by
  intros B e x HB
  cases HB with
  | appl₁ _ IH
  | appl₂ _ IH
  | binaryl₁ _ _ IH
  | binaryl₂ _ _ IH
  | lets _ IH
  | storel₁ _ IH
  | storel₂ _ IH => simp; apply closedb_opening_id; apply IH
  | appr₁ _ Hvalue
  | appr₂ _ Hvalue
  | binaryr₁ _ _ Hvalue
  | binaryr₂ _ _ Hvalue
  | storer₁ _ Hvalue
  | storer₂ _ Hvalue => simp; apply closedb_opening_id; apply value_lc; apply Hvalue
  | lift| load₁| alloc₁| load₂| alloc₂| fix₁| fix₂ => simp
  | ifz₁ _ _ IH₀ IH₁
  | ifz₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply closedb_opening_id; apply IH₀
    apply closedb_opening_id; apply IH₁

theorem subst𝔹 : ∀ B e₀ e₁ v x, ctx𝔹 B → closed_at B⟦e₀⟧ x → subst x v B⟦e₁⟧ = B⟦subst x v e₁⟧ :=
  by
  intros _ _ _ _ _ HB He₀
  cases HB with
  | appl₁| appl₂| binaryl₁| binaryl₂| lets| storel₁| storel₂ =>
    simp; apply subst_closed_id; apply He₀.right
  | appr₁| appr₂| binaryr₁| binaryr₂| storer₁| storer₂ =>
    simp; apply subst_closed_id; apply He₀.left
  | lift| load₁| alloc₁| load₂| alloc₂| fix₁| fix₂ => simp
  | ifz₁| ifz₂ =>
    simp; constructor
    apply subst_closed_id; apply He₀.right.left
    apply subst_closed_id; apply He₀.right.right

-- properties of ℝ contexts

theorem lc_ctxℝ : ∀ R e n intro lvl, ctxℝ intro lvl R → closedb_at e n → closedb_at R⟦e⟧ n :=
  by
  intros _ _ _ _ _ HR Hlc
  cases HR with
  | lam𝕔 =>
    apply close_closedb; omega
    apply closedb_inc; apply Hlc; omega
  | let𝕔 _ Hlcb =>
    constructor
    apply closedb_inc; apply Hlcb; omega
    apply close_closedb; omega
    apply closedb_inc; apply Hlc; omega
  | run =>
    apply Hlc
  | ifzl₂ _ _ Hvalue Hlcr =>
    constructor; apply closedb_inc; apply value_lc; apply Hvalue; omega
    constructor; apply closedb_inc; apply Hlc; omega
    apply closedb_inc; apply Hlcr; omega
  | ifzr₂ _ _ Hvalue₀ Hvalue₁ =>
    constructor; apply closedb_inc; apply value_lc; apply Hvalue₀; omega
    constructor; apply closedb_inc; apply value_lc; apply Hvalue₁; omega
    apply closedb_inc; apply Hlc; omega

theorem fv_atℝ :
  ∀ intro lvl R e₀ e₁,
    ctxℝ intro lvl R →
    fv e₁ ⊆ fv e₀ →
    fv R⟦e₁⟧ ⊆ fv R⟦e₀⟧ :=
  by
  intros intro lvl R e₀ e₁ HR Hsubst
  cases HR with
  | lam𝕔 =>
    simp
    rw [fv_closing, fv_closing]
    apply Set.diff_subset_diff_left
    apply Hsubst
  | let𝕔 =>
    simp
    rw [fv_closing, fv_closing]
    apply Set.subset_union_of_subset_right
    apply Set.diff_subset_diff_left
    apply Hsubst
  | run => apply Hsubst
  | ifzl₂ =>
    simp; constructor
    rw [Set.union_assoc]; simp
    apply Set.subset_union_of_subset_left
    apply Set.subset_union_of_subset_right
    apply Hsubst
  | ifzr₂ =>
    simp
    apply Set.subset_union_of_subset_right
    apply Hsubst

-- properties of 𝕄 contexts

theorem lc_ctx𝕄 : ∀ M e n lvl, ctx𝕄 lvl M → closedb_at e n → closedb_at M⟦e⟧ n :=
  by
  intros _ _ _ _ HM Hlc
  induction HM with
  | hole => apply Hlc
  | cons𝔹 _ _ HB _ IHlc => simp; apply lc_ctx𝔹; apply HB; apply IHlc
  | consℝ _ _ HR _ IHlc => simp; apply lc_ctxℝ; apply HR; apply IHlc

theorem fv_at𝕄 :
  ∀ lvl M e₀ e₁,
    ctx𝕄 lvl M →
    fv e₁ ⊆ fv e₀ →
    fv M⟦e₁⟧ ⊆ fv M⟦e₀⟧ :=
  by
  intros lvl M e₀ e₁ HM Hsubst
  induction HM with
  | hole => apply Hsubst
  | cons𝔹 _ _ HB _ IH =>
    simp; apply fv_at𝔹
    apply HB; apply IH
  | consℝ _ _ HR _ IH =>
    simp; apply fv_atℝ
    apply HR; apply IH

-- properties of 𝔼 contexts

theorem lc_ctx𝔼 : ∀ E e n, ctx𝔼 E → closedb_at e n → closedb_at E⟦e⟧ n :=
  by
  intros _ _ _ HE Hlc
  induction HE with
  | hole => apply Hlc
  | cons𝔹 _ _ HB _ IHlc => simp; apply lc_ctx𝔹; apply HB; apply IHlc

theorem closed_at_decompose𝔼 : ∀ E e₀ x, ctx𝔼 E → closed_at E⟦e₀⟧ x → closed_at e₀ x :=
  by
  intros _ _ _ HE Hclose
  induction HE with
  | hole => apply Hclose
  | cons𝔹 _ _ HB _ IH =>
    apply IH; apply closed_at_decompose𝔹
    apply HB; apply Hclose

theorem closed_at𝔼 : ∀ E e₀ e₁ x, ctx𝔼 E → closed_at E⟦e₀⟧ x → closed_at e₁ x → closed_at E⟦e₁⟧ x :=
  by
  intros _ _ _ _ HE He₀ He₁
  induction HE with
  | hole => apply He₁
  | cons𝔹 _ _ HB _ IH =>
    simp; apply closed_at𝔹; apply HB; apply He₀
    apply IH; apply closed_at_decompose𝔹; apply HB; apply He₀

theorem fv_at𝔼 :
  ∀ E e₀ e₁,
    ctx𝔼 E →
    fv e₁ ⊆ fv e₀ →
    fv E⟦e₁⟧ ⊆ fv E⟦e₀⟧ :=
  by
  intros E e₀ e₁ HE Hsubst
  induction HE with
  | hole => apply Hsubst
  | cons𝔹 _ _ HB _ IH =>
    simp; apply fv_at𝔹
    apply HB; apply IH

theorem fv_decompose𝔼 : ∀ E e, ctx𝔼 E → fv e ⊆ fv E⟦e⟧ :=
  by
  intros _ _ HE
  induction HE with
  | hole => rfl
  | cons𝔹 _ _ HB _ IH =>
    apply Set.Subset.trans; apply IH
    apply fv_decompose𝔹; apply HB

theorem open_ctx𝔼_map : ∀ E e x, ctx𝔼 E → open₀ x E⟦e⟧ = E⟦open₀ x e⟧ :=
  by
  intros _ _ _ HE
  induction HE with
  | hole => rfl
  | cons𝔹 _ _ HB _ IH =>
    simp at *; rw [← IH]
    apply open_ctx𝔹_map; apply HB

theorem subst𝔼 : ∀ E e₀ e₁ v x, ctx𝔼 E → closed_at E⟦e₀⟧ x → subst x v E⟦e₁⟧ = E⟦subst x v e₁⟧ :=
  by
  intros _ _ _ _ _ HE He₀
  induction HE with
  | hole => simp
  | cons𝔹 _ E HB _ IH =>
    simp at *; rw [← IH]; apply subst𝔹
    apply HB; apply He₀
    cases HB with
    | appl₁| appl₂| binaryl₁| binaryl₂| lets| storel₁| storel₂ => apply He₀.left
    | appr₁| appr₂| binaryr₁| binaryr₂| storer₁| storer₂ => apply He₀.right
    | lift| load₁| alloc₁| load₂| alloc₂| fix₁| fix₂ => apply He₀
    | ifz₁| ifz₂ => apply He₀.left

-- properties of ℚ contexts

theorem lc_ctxℚ : ∀ Q e n lvl, ctxℚ lvl Q → closedb_at e n → closedb_at Q⟦e⟧ n :=
  by
  intros _ _ _ _ HQ Hlc
  induction HQ with
  | holeℝ _ HR => apply lc_ctxℝ; apply HR; apply Hlc
  | cons𝔹 _ _ HB _ IHlc => simp; apply lc_ctx𝔹; apply HB; apply IHlc
  | consℝ _ _ HR _ IHlc => simp; apply lc_ctxℝ; apply HR; apply IHlc

theorem fv_atℚ :
  ∀ lvl Q e₀ e₁,
    ctxℚ lvl Q →
    fv e₁ ⊆ fv e₀ →
    fv Q⟦e₁⟧ ⊆ fv Q⟦e₀⟧ :=
  by
  intros lvl Q e₀ e₁ HQ Hsubst
  induction HQ with
  | holeℝ _ HR =>
    apply fv_atℝ
    apply HR; apply Hsubst
  | cons𝔹 _ _ HB _ IH =>
    simp; apply fv_at𝔹
    apply HB; apply IH
  | consℝ _ _ HR _ IH =>
    simp; apply fv_atℝ
    apply HR; apply IH

inductive head𝕄 : Expr → Expr → Prop where
  | lets : ∀ e v, value v → head𝕄 (.lets v e) (open_subst v e)
  | app₁ : ∀ e v, value v → head𝕄 (.app₁ (.lam e) v) (open_subst v e)
  | app₂ : ∀ f arg, head𝕄 (.app₂ (.code f) (.code arg)) (.reflect (.app₁ f arg))
  | binary₁ : ∀ op l r, head𝕄 (.binary₁ op (.lit l) (.lit r)) (.lit (eval op l r))
  | binary₂ : ∀ op l r, head𝕄 (.binary₂ op (.code l) (.code r)) (.reflect (.binary₁ op l r))
  | lift_lit : ∀ n, head𝕄 (.lift (.lit n)) (.reflect (.lit n))
  | lift_unit : head𝕄 (.lift .unit) (.reflect .unit)
  | lift_lam : ∀ e, head𝕄 (.lift (.lam e)) (.lam𝕔 (map𝕔₀ e))
  | lam𝕔 : ∀ e, head𝕄 (.lam𝕔 (.code e)) (.reflect (.lam e))
  | let𝕔 : ∀ b e, head𝕄 (.let𝕔 b (.code e)) (.code (.lets b e))
  | run : ∀ e, head𝕄 (.run (.code e)) e
  | load₂ : ∀ e, head𝕄 (.load₂ (.code e)) (.reflect (.load₁ e))
  | alloc₂ : ∀ e, head𝕄 (.alloc₂ (.code e)) (.reflect (.alloc₁ e))
  | store₂ : ∀ l r, head𝕄 (.store₂ (.code l) (.code r)) (.reflect (.store₁ l r))
  | ifz₁_left : ∀ l r, head𝕄 (.ifz₁ (.lit 0) l r) l
  | ifz₁_right : ∀ l r n, head𝕄 (.ifz₁ (.lit (.succ n)) l r) r
  | ifz₂ : ∀ c l r, head𝕄 (.ifz₂ (.code c) (.code l) (.code r)) (.reflect (.ifz₁ c l r))
  | fix₁ : ∀ e, head𝕄 (.fix₁ (.lam e)) (open_subst (.fix₁ (.lam e)) e)
  | fix₂ : ∀ e, head𝕄 (.fix₂ (.code e)) (.reflect (.fix₁ e))

inductive shead𝕄 : (Store × Expr) → (Store × Expr) → Prop where
  | load₁ : ∀ st l e, binds l e st → shead𝕄 (st, .load₁ (.loc l)) (st, e)
  | alloc₁ : ∀ st v, value v → shead𝕄 (st, .alloc₁ v) (v :: st, .loc (st.length))
  | store₁ : ∀ st₀ st₁ l v, value v → patch l v st₀ st₁ → shead𝕄 (st₀, .store₁ (.loc l) v) (st₁, .unit)

inductive step_lvl (lvl : ℕ) : (Store × Expr) → (Store × Expr) → Prop where
  | step𝕄 : ∀ M e₀ e₁ st, ctx𝕄 lvl M → lc e₀ → head𝕄 e₀ e₁ → step_lvl lvl (st, M⟦e₀⟧) (st, M⟦e₁⟧)
  | store𝕄 : ∀ M st₀ st₁ e₀ e₁, ctx𝕄 lvl M → lc e₀ → shead𝕄 (st₀, e₀) (st₁, e₁) → step_lvl lvl (st₀, M⟦e₀⟧) (st₁, M⟦e₁⟧)
  | reflect : ∀ P E b st, ctxℙ lvl P → ctx𝔼 E → lc b → step_lvl lvl (st, P⟦E⟦.reflect b⟧⟧) (st, P⟦.let𝕔 b E⟦.code (.bvar 0)⟧⟧)

@[simp]
def step : (Store × Expr) → (Store × Expr) → Prop :=
  step_lvl 0

inductive stepn : (Store × Expr) → (Store × Expr) → Prop
  | refl : ∀ e, stepn e e
  | multi : ∀ e₀ e₁ e₂, stepn e₀ e₁ → step e₁ e₂ → stepn e₀ e₂

-- properties of step

theorem step𝔹 : ∀ lvl B st₀ st₁ e₀ e₁, ctx𝔹 B → step_lvl lvl (st₀, e₀) (st₁, e₁) → ∃ e₂, step_lvl lvl (st₀, B⟦e₀⟧) (st₁, e₂) :=
  by
  intros lvl B st₀ st₁ e₀ e₁ HB Hstep
  cases Hstep with
  | step𝕄 M _ _ _ HM Hlc Hhead =>
    rw [ctx_comp B M]
    constructor; apply step_lvl.step𝕄
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hhead
  | store𝕄 M _ _ _ _ HM Hlc Hstore =>
    rw [ctx_comp B M]
    constructor; apply step_lvl.store𝕄
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hstore
  | reflect P E _ _ HP HE Hlc =>
    cases HP
    case hole =>
      constructor
      rw [ctx_swap B, ctx_comp B E]
      apply step_lvl.reflect
      apply ctxℙ.hole; apply ctx𝔼.cons𝔹
      apply HB; apply HE; apply Hlc
    case consℚ HQ =>
      constructor
      rw [ctx_comp B P]
      apply step_lvl.reflect
      apply ctxℙ.consℚ; apply ctxℚ.cons𝔹
      apply HB; apply HQ; apply HE; apply Hlc

theorem stepℝ : ∀ intro lvl R st₀ st₁ e₀ e₁, ctxℝ intro lvl R → step_lvl (lvl + intro) (st₀, e₀) (st₁, e₁) → step_lvl lvl (st₀, R⟦e₀⟧) (st₁, R⟦e₁⟧) :=
  by
  intros intro lvl R st₀ st₁ e₀ e₁ HR Hstep
  cases Hstep with
  | step𝕄 M _ _ _ HM Hlc Hhead =>
    repeat rw [ctx_comp R M]
    apply step_lvl.step𝕄
    apply ctx𝕄.consℝ; apply HR; apply HM
    apply Hlc; apply Hhead
  | store𝕄 M _ _ _ _ HM Hlc Hstore =>
    rw [ctx_comp R M]
    apply step_lvl.store𝕄
    apply ctx𝕄.consℝ; apply HR; apply HM
    apply Hlc; apply Hstore
  | reflect P _ _ _ HP HE Hlc =>
    cases HP
    case hole =>
      apply step_lvl.reflect
      apply ctxℙ.consℚ; apply ctxℚ.holeℝ
      apply HR; apply HE; apply Hlc
    case consℚ HQ =>
      rw [ctx_comp R P]
      apply step_lvl.reflect
      apply ctxℙ.consℚ; apply ctxℚ.consℝ
      apply HR; apply HQ; apply HE; apply Hlc

theorem fv_head𝕄 : ∀ e₀ e₁, head𝕄 e₀ e₁ → fv e₁ ⊆ fv e₀ :=
  by
  intros e₀ e₁ Hhead
  cases Hhead <;> simp
  case lets =>
    apply fv_opening
  case app₁ =>
    rw [Set.union_comm]
    apply fv_opening
  case lift_lam =>
    rw [← fv_maping𝕔]
  case fix₁ e =>
    have HEq : fv (.fix₁ (.lam e)) ∪ fv e = fv e := by simp
    rw [← HEq]
    apply fv_opening
