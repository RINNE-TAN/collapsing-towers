
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.Store
import CollapsingTowers.TwoLevel.OpenClose
import CollapsingTowers.TwoLevel.Neutral
import CollapsingTowers.TwoLevel.Env
abbrev Ctx :=
  Expr -> Expr

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
  | lit₂ : ctx𝔹 (fun X => .lit₂ X)
  | lam₂ : ctx𝔹 (fun X => .lam₂ X)
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
  | lit₂| lam₂ => apply Hlc

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
  | lit₂| lam₂ => apply HNeu

theorem closed_at_decompose𝔹 : ∀ B e₀ x, ctx𝔹 B -> closed_at B⟦e₀⟧ x -> closed_at e₀ x :=
  by
  intros _ _ _ HB Hclose
  cases HB with
  | appl₁| appl₂| plusl₁| plusl₂| lets =>
    apply Hclose.left
  | appr₁| appr₂| plusr₁| plusr₂ =>
    apply Hclose.right
  | lit₂| lam₂ => apply Hclose

theorem closed_at𝔹 : ∀ B e₀ e₁ x, ctx𝔹 B -> closed_at B⟦e₀⟧ x -> closed_at e₁ x -> closed_at B⟦e₁⟧ x :=
  by
  intros _ _ _ _ HB He₀ He₁
  cases HB with
  | appl₁| appl₂| plusl₁| plusl₂| lets =>
    constructor; apply He₁; apply He₀.right
  | appr₁| appr₂| plusr₁| plusr₂ =>
    constructor; apply He₀.left; apply He₁
  | lit₂| lam₂ => apply He₁

theorem neutral_db𝔹 : ∀ B e₀ e₁ i, ctx𝔹 B -> neutral_db i B⟦e₀⟧ -> neutral_db i e₁ -> neutral_db i B⟦e₁⟧ :=
  by
  intros _ _ _ _ HB He₀ He₁
  cases HB with
  | appl₁| appl₂| plusl₁| plusl₂| lets =>
    constructor; apply He₁; apply He₀.right
  | appr₁| appr₂| plusr₁| plusr₂ =>
    constructor; apply He₀.left; apply He₁
  | lit₂| lam₂ => apply He₁

theorem neutral𝔹 : ∀ B e₀ e₁ x, ctx𝔹 B -> neutral x B⟦e₀⟧ -> neutral x e₁ -> neutral x B⟦e₁⟧ :=
  by
  intros _ _ _ _ HB He₀ He₁
  cases HB with
  | appl₁| appl₂| plusl₁| plusl₂| lets =>
    constructor; apply He₁; apply He₀.right
  | appr₁| appr₂| plusr₁| plusr₂ =>
    constructor; apply He₀.left; apply He₁
  | lit₂| lam₂ => apply He₁

theorem subst𝔹 : ∀ B e₀ e₁ v x, ctx𝔹 B -> closed_at B⟦e₀⟧ x -> subst x v B⟦e₁⟧ = B⟦subst x v e₁⟧ :=
  by
  intros _ _ _ _ _ HB He₀
  cases HB with
  | appl₁| appl₂| plusl₁| plusl₂| lets =>
    simp; apply subst_closed_id; apply He₀.right
  | appr₁| appr₂| plusr₁| plusr₂ =>
    simp; apply subst_closed_id; apply He₀.left
  | lit₂| lam₂ => simp

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
  | lit₂| lam₂ => simp

inductive ctxℝ : ℕ -> Ctx -> Prop where
  | lam𝕔 : ctxℝ lvl (fun X => .lam𝕔 (close₀ lvl X))
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
    | lit₂| lam₂ => apply He₀

theorem open_ctx𝔼_map : ∀ E e x, ctx𝔼 E -> open₀ x E⟦e⟧ = E⟦open₀ x e⟧ :=
  by
  intros _ _ _ HE
  induction HE with
  | hole => rfl
  | cons𝔹 _ _ HB _ IH =>
    simp at *; rw [← IH]
    apply open_ctx𝔹_map; apply HB

inductive ℙℚ : Type where
  | ℙ
  | ℚ

inductive ctxℙℚ : ℙℚ -> ℕ -> Ctx -> Prop where
  | hole : ctxℙℚ .ℙ lvl id
  | cons𝔹 : ∀ B PQ, ctx𝔹 B -> ctxℙℚ .ℚ lvl PQ -> ctxℙℚ flag lvl (B ∘ PQ)
  | consℝ : ∀ R PQ, ctxℝ lvl R -> ctxℙℚ .ℙ (lvl + 1) PQ -> ctxℙℚ flag lvl (R ∘ PQ)

@[simp]
def ctxℙ : ℕ -> Ctx -> Prop := ctxℙℚ .ℙ

theorem lc_ctxℙ : ∀ P e n, ctxℙ n P -> lc e -> lc P⟦e⟧ :=
  by
  simp; generalize HPQ : ℙℚ.ℙ = PQ
  clear HPQ
  intros _ _ _ HP Hlc
  induction HP with
  | hole => apply Hlc
  | cons𝔹 _ _ HB _ IHlc => simp; apply lc_ctx𝔹; apply HB; apply IHlc
  | consℝ _ _ HR _ IHlc => simp; apply lc_ctxℝ; apply HR; apply IHlc

inductive head𝕄 : Expr -> Expr -> Prop where
  | lets : ∀ e v, value v -> head𝕄 (.lets v e) (open_subst v e)
  | app₁ : ∀ e v, value v -> head𝕄 (.app₁ (.lam₁ e) v) (open_subst v e)
  | app₂ : ∀ f arg, head𝕄 (.app₂ (.code f) (.code arg)) (.reflect (.app₁ f arg))
  | plus₁ : ∀ l r, head𝕄 (.plus₁ (.lit₁ l) (.lit₁ r)) (.lit₁ (l + r))
  | plus₂ : ∀ l r, head𝕄 (.plus₂ (.code l) (.code r)) (.reflect (.plus₁ l r))
  | lit₂ : ∀ n, head𝕄 (.lit₂ (.lit₁ n)) (.code (.lit₁ n))
  | lam₂ : ∀ e, head𝕄 (.lam₂ (.lam₁ e)) (.lam𝕔 (map𝕔₀ e))
  | lam𝕔 : ∀ e, head𝕄 (.lam𝕔 (.code e)) (.reflect (.lam₁ e))
  | let𝕔₀ : ∀ b e, head𝕄 (.let𝕔 b (.code e)) (.code (.lets b e))
  | let𝕔₁ : ∀ b n, head𝕄 (.let𝕔 b (.lit₁ n)) (.lit₁ n)
  | let𝕔₂ : ∀ b e, head𝕄 (.let𝕔 b (.lam₁ e)) (.lam₁ (.let𝕔 b (swapdb 0 1 e)))

inductive step_lvl (lvl: ℕ) : (Store × Expr) -> (Store × Expr) -> Prop where
  | step𝕄 : ∀ M e₀ e₁ st, ctx𝕄 lvl M -> lc e₀ -> head𝕄 e₀ e₁ -> step_lvl lvl (st, M⟦e₀⟧) (st, M⟦e₁⟧)
  | reflect : ∀ P E b st, ctxℙ lvl P -> ctx𝔼 E -> lc b -> step_lvl lvl (st, P⟦E⟦.reflect b⟧⟧) (st, P⟦.let𝕔 b E⟦.code (.bvar 0)⟧⟧)

theorem step𝔹 : ∀ lvl B e₀ e₁ st₀ st₁, ctx𝔹 B -> step_lvl lvl (st₀, e₀) (st₁, e₁) -> ∃ e₂, step_lvl lvl (st₀, B⟦e₀⟧) (st₁, e₂) :=
  by
  intros lvl B e₀ e₁ st₀ st₁ HB Hstep
  cases Hstep with
  | step𝕄 M _ _ _ HM Hlc Hhead =>
    rw [ctx_comp B M]
    constructor; apply step_lvl.step𝕄
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hhead
  | reflect P E _ _ HP HE Hlc =>
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

theorem stepℝ : ∀ lvl R e₀ e₁ st₀ st₁, ctxℝ lvl R -> step_lvl (lvl + 1) (st₀, e₀) (st₁, e₁) -> step_lvl lvl (st₀, R⟦e₀⟧) (st₁, R⟦e₁⟧) :=
  by
  intros lvl R e₀ e₁ st₀ st₁ HR Hstep
  cases Hstep with
  | step𝕄 M _ _ _ HM Hlc Hhead =>
    repeat rw [ctx_comp R M]
    apply step_lvl.step𝕄
    apply ctx𝕄.consℝ; apply HR; apply HM
    apply Hlc; apply Hhead
  | reflect P _ _ _ HP HE Hlc =>
    repeat rw [ctx_comp R P]
    apply step_lvl.reflect
    apply ctxℙℚ.consℝ; apply HR; apply HP
    apply HE; apply Hlc

@[simp]
def step : (Store × Expr) -> (Store × Expr) -> Prop := step_lvl 0

inductive stepn : (Store × Expr) -> (Store × Expr) → Prop
  | refl : ∀ st e, stepn (st, e) (st, e)
  | multi : ∀ st₁ st₂ st₃ e₁ e₂ e₃, stepn (st₁, e₁) (st₂, e₂) → step (st₂, e₂) (st₃, e₃) → stepn (st₁, e₁) (st₃, e₃)

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

def st : Store :=
  []

def x₀ : Expr :=
  .fvar 0

def x₁ : Expr :=
  .fvar 1

def x₂ : Expr :=
  .fvar 2

def x₃ : Expr :=
  .fvar 3

def expr₀ : Expr :=
  .lam₂ (.lam₁ (close₀ 0 (.plus₂ x₀ (.plus₂ x₀ x₀))))

def expr₁ : Expr :=
  .lam𝕔 (close₀ 0 (.plus₂ (.code x₀) (.plus₂ (.code x₀) (.code x₀))))

def expr₂ : Expr :=
  .lam𝕔 (close₀ 0 (.plus₂ (.code x₀) (.reflect (.plus₁ x₀ x₀))))

def expr₃ : Expr :=
  .lam𝕔 (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.plus₂ (.code x₀) (.code x₁)))))

def expr₄ : Expr :=
  .lam𝕔 (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.reflect (.plus₁ x₀ x₁)))))

def expr₅ : Expr :=
  .lam𝕔 (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.let𝕔 (.plus₁ x₀ x₁) (close₀ 2 (.code x₂))))))

def expr₆ : Expr :=
  .lam𝕔 (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.code (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))

def expr₇ : Expr :=
  .lam𝕔 (close₀ 0 (.code (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))

def expr₈ : Expr :=
  .reflect (.lam₁ (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))

def expr₉ : Expr :=
  .let𝕔 (.lam₁ (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))
    (close₀ 3 (.code x₃))

def expr𝕩 : Expr :=
  .code
    (.lets (.lam₁ (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂)))))) (close₀ 3 x₃))

example : step (st, expr₀) (st, expr₁) := by
  rw [expr₀]
  rw [expr₁]
  apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
  repeat constructor

example : step (st, expr₁) (st, expr₂) := by
  rw [expr₁]
  rw [expr₂]
  apply step_lvl.step𝕄 _ _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 (ctx𝕄.cons𝔹 _ _ (ctx𝔹.plusr₂ _ _) ctx𝕄.hole))
  repeat constructor

example : step (st, expr₂) (st, expr₃) := by
  rw [expr₂]
  rw [expr₃]
  apply step_lvl.reflect _ _ _ _ (ctxℙℚ.consℝ _ _ ctxℝ.lam𝕔 ctxℙℚ.hole) (ctx𝔼.cons𝔹 _ _ (ctx𝔹.plusr₂ _ _) ctx𝔼.hole)
  repeat constructor

example : step (st, expr₃) (st, expr₄) := by
  rw [expr₃]
  rw [expr₄]
  apply step_lvl.step𝕄 _ _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 (ctx𝕄.consℝ _ _ (ctxℝ.let𝕔 _ _) ctx𝕄.hole))
  repeat constructor

example : step (st, expr₄) (st, expr₅) := by
  rw [expr₄]
  rw [expr₅]
  apply step_lvl.reflect _ _ _ _ (ctxℙℚ.consℝ _ _ ctxℝ.lam𝕔 (ctxℙℚ.consℝ _ _ (ctxℝ.let𝕔 _ _) ctxℙℚ.hole)) ctx𝔼.hole
  repeat constructor

example : step (st, expr₅) (st, expr₆) := by
  rw [expr₅]
  rw [expr₆]
  apply step_lvl.step𝕄 _ _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 (ctx𝕄.consℝ _ _ (ctxℝ.let𝕔 _ _) ctx𝕄.hole))
  repeat constructor

example : step (st, expr₆) (st, expr₇) := by
  rw [expr₆]
  rw [expr₇]
  apply step_lvl.step𝕄 _ _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 ctx𝕄.hole)
  repeat constructor

example : step (st, expr₇) (st, expr₈) := by
  rw [expr₇]
  rw [expr₈]
  rw [x₀]
  rw [x₁]
  rw [x₂]
  simp
  apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
  repeat constructor

example : step (st, expr₈) (st, expr₉) := by
  rw [expr₈]
  rw [expr₉]
  apply step_lvl.reflect _ _ _ _ ctxℙℚ.hole ctx𝔼.hole
  repeat constructor

example : step (st, expr₉) (st, expr𝕩) := by
  rw [expr₉]
  rw [expr𝕩]
  apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
  repeat constructor
