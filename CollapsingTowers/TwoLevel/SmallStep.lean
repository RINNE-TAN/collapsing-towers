
import Mathlib.Data.Finset.Basic
import CollapsingTowers.TwoLevel.Syntax
import CollapsingTowers.TwoLevel.OpenClose
import CollapsingTowers.TwoLevel.Neutral
import CollapsingTowers.TwoLevel.Env

abbrev Ctx := Expr -> Expr

theorem ctx_comp : (f g : Ctx) -> ∀ e, f (g e) = (f ∘ g) e := by simp

theorem ctx_swap : (f : Ctx) -> ∀ e, f (id e) = id (f e) := by simp

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
  | lift : ctx𝔹 (fun X => .lift X)
  | lets : ∀ e, closedb_at e 1 -> ctx𝔹 (fun X => .lets X e)

inductive ctxℝ : ℕ -> Ctx -> Prop where
  | lam𝕔 : ctxℝ lvl (fun X => .lam𝕔 (close₀ lvl X))
  | let𝕔 : ∀ b, lc b -> ctxℝ lvl (fun X => .let𝕔 b (close₀ lvl X))

inductive ctx𝕄 : ℕ -> Ctx -> Prop where
  | hole : ctx𝕄 lvl id
  | cons𝔹 : ∀ B M, ctx𝔹 B -> ctx𝕄 lvl M -> ctx𝕄 lvl (B ∘ M)
  | consℝ : ∀ R M, ctxℝ lvl R -> ctx𝕄 (lvl + 1) M -> ctx𝕄 lvl (R ∘ M)

inductive ctx𝔼 : Ctx -> Prop where
  | hole : ctx𝔼 id
  | cons𝔹 : ∀ B E, ctx𝔹 B -> ctx𝔼 E -> ctx𝔼 (B ∘ E)

inductive ℙℚ : Type where
  | ℙ
  | ℚ

inductive ctxℙℚ : ℙℚ -> ℕ -> Ctx -> Prop where
  | hole : ctxℙℚ .ℙ lvl id
  | cons𝔹 : ∀ B PQ, ctx𝔹 B -> ctxℙℚ .ℚ lvl PQ -> ctxℙℚ flag lvl (B ∘ PQ)
  | consℝ : ∀ R PQ, ctxℝ lvl R -> ctxℙℚ .ℙ (lvl + 1) PQ -> ctxℙℚ flag lvl (R ∘ PQ)

@[simp]
def ctxℙ : ℕ -> Ctx -> Prop := ctxℙℚ .ℙ

inductive head𝕄 : Expr -> Expr -> Prop where
  | lets : ∀ e v, value v -> head𝕄 (.lets v e) (open_subst v e)
  | app₁ : ∀ e v, value v -> head𝕄 (.app₁ (.lam₁ e) v) (open_subst v e)
  | app₂ : ∀ f arg, head𝕄 (.app₂ (.code f) (.code arg)) (.reflect (.app₁ f arg))
  | plus₁ : ∀ l r, head𝕄 (.plus₁ (.lit₁ l) (.lit₁ r)) (.lit₁ (l + r))
  | plus₂ : ∀ l r, head𝕄 (.plus₂ (.code l) (.code r)) (.reflect (.plus₁ l r))
  | lift_lit : ∀ n, head𝕄 (.lift (.lit₁ n)) (.code (.lit₁ n))
  | lift_lam : ∀ e, head𝕄 (.lift (.lam₁ e)) (.lam𝕔 (map𝕔₀ e))
  | lam𝕔 : ∀ e, head𝕄 (.lam𝕔 (.code e)) (.reflect (.lam₁ e))
  | let𝕔₀ : ∀ b e, head𝕄 (.let𝕔 b (.code e)) (.code (.lets b e))
  | let𝕔₁ : ∀ b n, head𝕄 (.let𝕔 b (.lit₁ n)) (.lit₁ n)
  | let𝕔₂ : ∀ b e, head𝕄 (.let𝕔 b (.lam₁ e)) (.lam₁ (.let𝕔 b (swapdb 0 1 e)))

inductive step_lvl (lvl: ℕ) : Expr -> Expr -> Prop where
  | step𝕄 : ∀ M e₀ e₁, ctx𝕄 lvl M -> lc e₀ -> head𝕄 e₀ e₁ -> step_lvl lvl M⟦e₀⟧ M⟦e₁⟧
  | reflect : ∀ P E b, ctxℙ lvl P -> ctx𝔼 E -> lc b -> step_lvl lvl P⟦E⟦.reflect b⟧⟧ P⟦.let𝕔 b E⟦.code (.bvar 0)⟧⟧

@[simp]
def step : Expr -> Expr -> Prop := step_lvl 0

inductive stepn : Expr → Expr → Prop
  | refl : ∀ e, stepn e e
  | multi : ∀ e₁ e₂ e₃, stepn e₁ e₂ → step e₂ e₃ → stepn e₁ e₃

----------------

lemma stepn.trans : ∀ t1 t2 t3, stepn t1 t2 → stepn t2 t3 → stepn t1 t3 := by
  intros t1 t2 t3 h1 h2; induction h2
  . assumption
  . case _ _ _ hstn hst ih =>
    apply stepn.multi; apply ih; assumption

lemma stepn.multi' : ∀ t1 t2 t3, step t1 t2 → stepn t2 t3 → stepn t1 t3 := by
  intros t1 t2 t3 st1 st2
  have st3 : stepn t1 t1 := by constructor
  have st4 : stepn t1 t2 := by apply stepn.multi; assumption; apply st1
  apply stepn.trans; assumption; assumption

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

theorem neutral_ctx𝔹 : ∀ B e x, ctx𝔹 B -> neutral x B⟦e⟧ -> neutral x e :=
  by
  intros B e x HB HNeu
  induction HB with
  | appl₁ _ IH
  | appl₂ _ IH
  | plusl₁ _ IH
  | plusl₂ _ IH
  | lets _ IH => apply HNeu.left
  | appr₁ _ Hvalue
  | appr₂ _ Hvalue
  | plusr₁ _ Hvalue
  | plusr₂ _ Hvalue => apply HNeu.right
  | lift => apply HNeu

theorem closed_at_decompose𝔹 : ∀ B e₀ x, ctx𝔹 B -> closed_at B⟦e₀⟧ x -> closed_at e₀ x :=
  by
  intros _ _ _ HB Hclose
  cases HB with
  | appl₁| appl₂| plusl₁| plusl₂| lets =>
    apply Hclose.left
  | appr₁| appr₂| plusr₁| plusr₂ =>
    apply Hclose.right
  | lift => apply Hclose

theorem closed_at𝔹 : ∀ B e₀ e₁ x, ctx𝔹 B -> closed_at B⟦e₀⟧ x -> closed_at e₁ x -> closed_at B⟦e₁⟧ x :=
  by
  intros _ _ _ _ HB He₀ He₁
  cases HB with
  | appl₁| appl₂| plusl₁| plusl₂| lets =>
    constructor; apply He₁; apply He₀.right
  | appr₁| appr₂| plusr₁| plusr₂ =>
    constructor; apply He₀.left; apply He₁
  | lift => apply He₁

theorem neutral_db𝔹 : ∀ B e₀ e₁ i, ctx𝔹 B -> neutral_db i B⟦e₀⟧ -> neutral_db i e₁ -> neutral_db i B⟦e₁⟧ :=
  by
  intros _ _ _ _ HB He₀ He₁
  cases HB with
  | appl₁| appl₂| plusl₁| plusl₂| lets =>
    constructor; apply He₁; apply He₀.right
  | appr₁| appr₂| plusr₁| plusr₂ =>
    constructor; apply He₀.left; apply He₁
  | lift => apply He₁

theorem neutral𝔹 : ∀ B e₀ e₁ x, ctx𝔹 B -> neutral x B⟦e₀⟧ -> neutral x e₁ -> neutral x B⟦e₁⟧ :=
  by
  intros _ _ _ _ HB He₀ He₁
  cases HB with
  | appl₁| appl₂| plusl₁| plusl₂| lets =>
    constructor; apply He₁; apply He₀.right
  | appr₁| appr₂| plusr₁| plusr₂ =>
    constructor; apply He₀.left; apply He₁
  | lift => apply He₁

theorem subst𝔹 : ∀ B e₀ e₁ v x, ctx𝔹 B -> closed_at B⟦e₀⟧ x -> subst x v B⟦e₁⟧ = B⟦subst x v e₁⟧ :=
  by
  intros _ _ _ _ _ HB He₀
  cases HB with
  | appl₁| appl₂| plusl₁| plusl₂| lets =>
    simp; apply subst_closed_id; apply He₀.right
  | appr₁| appr₂| plusr₁| plusr₂ =>
    simp; apply subst_closed_id; apply He₀.left
  | lift => simp

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
  | lift => simp

-- properties of ℝ contexts

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

-- properties of 𝕄 contexts

theorem lc_ctx𝕄 : ∀ M e n, ctx𝕄 n M -> lc e -> lc M⟦e⟧ :=
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

theorem closed_at_decompose𝔼 : ∀ E e₀ x, ctx𝔼 E -> closed_at E⟦e₀⟧ x -> closed_at e₀ x :=
  by
  intros _ _ _ HE Hclose
  induction HE with
  | hole => apply Hclose
  | cons𝔹 _ _ HB _ IH =>
    apply IH; apply closed_at_decompose𝔹
    apply HB; apply Hclose

theorem closed_at𝔼 : ∀ E e₀ e₁ x, ctx𝔼 E -> closed_at E⟦e₀⟧ x -> closed_at e₁ x -> closed_at E⟦e₁⟧ x :=
  by
  intros _ _ _ _ HE He₀ He₁
  induction HE with
  | hole => apply He₁
  | cons𝔹 _ _ HB _ IH =>
    simp; apply closed_at𝔹; apply HB; apply He₀
    apply IH; cases HB <;> simp at He₀
    repeat
      first
      | apply He₀.left
      | apply He₀.right
      | apply He₀

theorem neutral_db𝔼 : ∀ E e₀ e₁ i, ctx𝔼 E -> neutral_db i E⟦e₀⟧ -> neutral_db i e₁ -> neutral_db i E⟦e₁⟧ :=
  by
  intros _ _ _ _ HE He₀ He₁
  induction HE with
  | hole => apply He₁
  | cons𝔹 _ _ HB _ IH =>
    simp; apply neutral_db𝔹; apply HB; apply He₀
    apply IH; cases HB <;> simp at He₀
    repeat
      first
      | apply He₀.left
      | apply He₀.right
      | apply He₀

theorem neutral𝔼 : ∀ E e₀ e₁ x, ctx𝔼 E -> neutral x E⟦e₀⟧ -> neutral x e₁ -> neutral x E⟦e₁⟧ :=
  by
  intros _ _ _ _ HE He₀ He₁
  induction HE with
  | hole => apply He₁
  | cons𝔹 _ _ HB _ IH =>
    simp; apply neutral𝔹; apply HB; apply He₀
    apply IH; cases HB <;> simp at He₀
    repeat
      first
      | apply He₀.left
      | apply He₀.right
      | apply He₀

theorem subst𝔼 : ∀ E e₀ e₁ v x, ctx𝔼 E -> closed_at E⟦e₀⟧ x -> subst x v E⟦e₁⟧ = E⟦subst x v e₁⟧ :=
  by
  intros _ _ _ _ _ HE He₀
  induction HE with
  | hole => simp
  | cons𝔹 _ E HB _ IH =>
    simp at *; rw [← IH]; apply subst𝔹
    apply HB; apply He₀
    cases HB with
    | appl₁| appl₂| plusl₁| plusl₂| lets => apply He₀.left
    | appr₁| appr₂| plusr₁| plusr₂ => apply He₀.right
    | lift => apply He₀

theorem open_ctx𝔼_map : ∀ E e x, ctx𝔼 E -> open₀ x E⟦e⟧ = E⟦open₀ x e⟧ :=
  by
  intros _ _ _ HE
  induction HE with
  | hole => rfl
  | cons𝔹 _ _ HB _ IH =>
    simp at *; rw [← IH]
    apply open_ctx𝔹_map; apply HB

-- properties of ℙ contexts

theorem lc_ctxℙ : ∀ P e n, ctxℙ n P -> lc e -> lc P⟦e⟧ :=
  by
  simp; generalize HPQ : ℙℚ.ℙ = PQ
  clear HPQ
  intros _ _ _ HP Hlc
  induction HP with
  | hole => apply Hlc
  | cons𝔹 _ _ HB _ IHlc => simp; apply lc_ctx𝔹; apply HB; apply IHlc
  | consℝ _ _ HR _ IHlc => simp; apply lc_ctxℝ; apply HR; apply IHlc

theorem step𝔹 : ∀ lvl B e₀ e₁, ctx𝔹 B -> step_lvl lvl e₀ e₁ -> ∃ e₂, step_lvl lvl (B e₀) e₂ :=
  by
  intros lvl B e₀ e₁ HB Hstep
  cases Hstep with
  | step𝕄 M _ _ HM Hlc Hhead =>
    rw [ctx_comp B M]
    constructor; apply step_lvl.step𝕄
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hhead
  | reflect P E _ HP HE Hlc =>
    cases HP with
    | hole =>
      constructor
      rw [ctx_swap B, ctx_comp B E]
      apply step_lvl.reflect
      apply ctxℙℚ.hole
      apply ctx𝔼.cons𝔹
      apply HB; apply HE; apply Hlc
    | cons𝔹 _ _ IHB HPQ =>
      constructor
      rw [ctx_comp B]
      apply step_lvl.reflect
      apply ctxℙℚ.cons𝔹; apply HB
      apply ctxℙℚ.cons𝔹; apply IHB
      apply HPQ; apply HE; apply Hlc
    | consℝ _ _ HR HPQ =>
      constructor
      rw [ctx_comp B]
      apply step_lvl.reflect
      apply ctxℙℚ.cons𝔹; apply HB
      apply ctxℙℚ.consℝ; apply HR
      apply HPQ; apply HE; apply Hlc

theorem stepℝ : ∀ lvl R e₀ e₁, ctxℝ lvl R -> step_lvl (lvl + 1) e₀ e₁ -> step_lvl lvl (R e₀) (R e₁) :=
  by
  intros lvl R e₀ e₁ HR Hstep
  cases Hstep with
  | step𝕄 M _ _ HM Hlc Hhead =>
    repeat rw [ctx_comp R M]
    apply step_lvl.step𝕄
    apply ctx𝕄.consℝ; apply HR; apply HM
    apply Hlc; apply Hhead
  | reflect P _ _ HP HE Hlc =>
    repeat rw [ctx_comp R P]
    apply step_lvl.reflect
    apply ctxℙℚ.consℝ; apply HR; apply HP
    apply HE; apply Hlc
