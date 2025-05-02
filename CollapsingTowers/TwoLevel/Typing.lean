
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.OpenClose
import CollapsingTowers.TwoLevel.SmallStep
import CollapsingTowers.TwoLevel.Env
@[simp]
def binds (x : ℕ) (τ : Ty) (Γ : TEnv) :=
  indexr x Γ = some τ

theorem binds_extend : ∀ Γ Δ x τ, binds x τ Γ -> binds x τ (Δ ++ Γ) :=
  by
  intros Γ Δ x τ Hbinds
  induction Δ with
  | nil => apply Hbinds
  | cons head tails IHtails =>
    simp
    by_cases Hx : x = tails.length + Γ.length
    . have Hx : x < Γ.length := by apply indexrSome'; exists τ
      omega
    . rw [if_neg Hx]; apply IHtails

inductive typing : TEnv -> Expr -> Ty -> Prop where
  | fvar : ∀ Γ x τ,
    binds x τ Γ ->
    typing Γ (.fvar x) τ
  | lam₁ : ∀ Γ e τ𝕒 τ𝕓,
    typing (τ𝕒 :: Γ) (open₀ Γ.length e) τ𝕓 ->
    closed_at e Γ.length ->
    typing Γ (.lam₁ e) (.arrow τ𝕒 τ𝕓)
  | lam₂ : ∀ Γ e τ𝕒 τ𝕓,
    typing (.rep τ𝕒 :: Γ) (open₀ Γ.length e) (.rep τ𝕓) ->
    closed_at e Γ.length ->
    typing Γ (.lam₂ e) (.rep (.arrow τ𝕒 τ𝕓))
  | app₁ : ∀ Γ f arg τ𝕒 τ𝕓,
    typing Γ f (.arrow τ𝕒 τ𝕓) ->
    typing Γ arg τ𝕒 ->
    typing Γ (.app₁ f arg) τ𝕓
  | app₂ : ∀ Γ f arg τ𝕒 τ𝕓,
    typing Γ f (.rep (.arrow τ𝕒 τ𝕓)) ->
    typing Γ arg (.rep τ𝕒) ->
    typing Γ (.app₂ f arg) (.rep τ𝕓)
  | plus₁ : ∀ Γ l r,
    typing Γ l .nat ->
    typing Γ r .nat ->
    typing Γ (.plus₁ l r) .nat
  | plus₂ : ∀ Γ l r,
    typing Γ l (.rep .nat) ->
    typing Γ r (.rep .nat) ->
    typing Γ (.plus₂ l r) (.rep .nat)
  | lit₁ : ∀ Γ n,
    typing Γ (.lit₁ n) .nat
  | lit₂ : ∀ Γ n,
    typing Γ (.lit₂ n) (.rep .nat)
  | code : ∀ Γ e τ,
    typing Γ e τ ->
    typing Γ (.code e) (.rep τ)
  | reflect : ∀ Γ e τ,
    typing Γ e τ ->
    typing Γ (.reflect e) (.rep τ)
  | lam𝕔 : ∀ Γ e τ𝕒 τ𝕓,
    typing (τ𝕒 :: Γ) (open₀ Γ.length e) (.rep τ𝕓) ->
    closed_at e Γ.length ->
    typing Γ (.lam𝕔 e) (.rep (.arrow τ𝕒 τ𝕓))
  | lets : ∀ Γ b e τ𝕒 τ𝕓,
    typing Γ b τ𝕒 ->
    typing (τ𝕒 :: Γ) (open₀ Γ.length e) τ𝕓 ->
    closed_at e Γ.length ->
    typing Γ (.lets b e) τ𝕓
  | let𝕔 : ∀ Γ b e τ𝕒 τ𝕓,
    typing Γ b τ𝕒 ->
    typing (τ𝕒 :: Γ) (open₀ Γ.length e) τ𝕓 ->
    closed_at e Γ.length ->
    typing Γ (.let𝕔 b e) τ𝕓

example : typing [] expr₀ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₀, x₀]
  repeat constructor

example : typing [] expr₁ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₁, x₀]
  repeat constructor

example : typing [] expr₂ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₂, x₀]
  repeat constructor

example : typing [] expr₃ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₃, x₀, x₁]
  repeat constructor

example : typing [] expr₄ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₄, x₀, x₁]
  repeat constructor

example : typing [] expr₅ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₅, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr₆ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₆, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr₇ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₇, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr₈ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₈, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr₉ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₉, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr𝕩 (.rep (.arrow .nat .nat)) :=
  by
  rw [expr𝕩, x₀, x₁, x₂]
  repeat constructor

theorem typing_regular : ∀ Γ e τ, typing Γ e τ -> lc e :=
  by
  intros Γ e τ Htyping
  induction Htyping with
  | fvar
  | lit₁
  | lit₂ => constructor
  | lam₁ _ _ _ _ _ _ IHe
  | lam₂ _ _ _ _ _ _ IHe
  | lam𝕔 _ _ _ _ _ _ IHe => apply open_closed; apply IHe
  | app₁ _ _ _ _ _ _ _ IH₀ IH₁
  | app₂ _ _ _ _ _ _ _ IH₀ IH₁
  | plus₁ _ _ _ _ _ IH₀ IH₁
  | plus₂ _ _ _ _ _ IH₀ IH₁ => constructor; apply IH₀; apply IH₁
  | code _ _ _ _ IH
  | reflect _ _ _ _ IH => apply IH
  | lets _ _ _ _ _ _ _ _ IH₀ IH₁
  | let𝕔 _ _ _ _ _ _ _ _ IH₀ IH₁ => constructor; apply IH₀; apply open_closed; apply IH₁

theorem typing_closed : ∀ Γ e τ, typing Γ e τ -> closed_at e Γ.length :=
  by
  intros Γ e τ Htyping
  induction Htyping with
  | fvar _ _ τ Hbind => simp at *; apply indexrSome'; exists τ
  | lam₁ _ _ _ _ _ IH
  | lam₂ _ _ _ _ _ IH
  | lam𝕔 _ _ _ _ _ IH
  | code _ _ _ _ IH
  | reflect _ _ _ _ IH => apply IH
  | app₁ _ _ _ _ _ _ _ IH₀ IH₁
  | app₂ _ _ _ _ _ _ _ IH₀ IH₁
  | plus₁ _ _ _ _ _ IH₀ IH₁
  | plus₂ _ _ _ _ _ IH₀ IH₁ => constructor; apply IH₀; apply IH₁
  | lets _ _ _ _ _ _ _ IH₀ IH₁
  | let𝕔 _ _ _ _ _ _ _ IH₀ IH₁ => constructor; apply IH₁; apply IH₀
  | lit₁| lit₂ => constructor

theorem typing_extend : ∀ Γ Δ e τ, typing Γ e τ -> typing (Δ ++ Γ) e τ :=
  by
  intros Γ Δ e τ Hτ
  induction Hτ generalizing Δ with
  | fvar _ _ _ Hbinds => constructor; apply binds_extend; apply Hbinds
  | _ => admit

theorem typing𝔹 : ∀ Γ B e τ, ctx𝔹 B -> typing Γ (B e) τ -> ∃ τ, typing Γ e τ :=
  by
  intros Γ B e τ HB
  cases HB
  all_goals
    intro Hτ; cases Hτ
    next H₀ H₁ H₂ =>
      constructor
      first
      | apply H₀
      | apply H₁
      | apply H₂

theorem typing𝔼 : ∀ Γ E e τ, ctx𝔼 E -> typing Γ (E e) τ -> ∃ τ, typing Γ e τ :=
  by
  intros _ _ _ τ HE
  induction HE generalizing τ with
  | hole => intro; exists τ
  | cons𝔹 _ _ HB HE IH =>
    intro Hτ
    have ⟨τ, Hτ⟩ := typing𝔹 _ _ _ _ HB Hτ
    apply IH; apply Hτ

theorem preservationℝ :
    ∀ Γ R e₀ e₁,
      ctxℝ Γ.length R ->
        lc e₀ ->
          (∀ τ𝕒 τ𝕓, typing (τ𝕒 :: Γ) e₀ τ𝕓 -> typing (τ𝕒 :: Γ) e₁ τ𝕓) -> ∀ τ, typing Γ (R e₀) τ -> typing Γ (R e₁) τ :=
  by
  intro Γ _ e₀ e₁ HR Hlc HτMap _ Hτe₀
  cases HR with
  | lam𝕔 =>
    cases Hτe₀ with
    | lam𝕔 _ _ _ _ Hτe₀ =>
      have Hopen_close_e₀ := open_close_id₀ e₀ Γ.length Hlc
      rw [Hopen_close_e₀] at Hτe₀
      have Hτe₁ := HτMap _ _ Hτe₀
      have Hopen_close_e₀ := open_close_id₀ e₁ Γ.length (typing_regular _ _ _ Hτe₁)
      constructor
      rw [Hopen_close_e₀]
      apply Hτe₁
      apply close_closed
      apply typing_closed _ _ _ Hτe₁
  | let𝕔 =>
    cases Hτe₀ with
    | let𝕔 _ _ _ _ _ Hτb Hτe₀ =>
      have Hopen_close_e₀ := open_close_id₀ e₀ Γ.length Hlc
      rw [Hopen_close_e₀] at Hτe₀
      have Hτe₁ := HτMap _ _ Hτe₀
      have Hopen_close_e₀ := open_close_id₀ e₁ Γ.length (typing_regular _ _ _ Hτe₁)
      constructor
      apply Hτb
      rw [Hopen_close_e₀]
      apply Hτe₁
      apply close_closed
      apply typing_closed _ _ _ Hτe₁

theorem preservation𝔹 :
    ∀ Γ B e₀ e₁, ctx𝔹 B -> (∀ τ, typing Γ e₀ τ -> typing Γ e₁ τ) -> ∀ τ, typing Γ (B e₀) τ -> typing Γ (B e₁) τ :=
  by
  intro _ _ _ _ HB HτMap _ Hτe₀
  cases HB
  all_goals
    cases Hτe₀
    next H₀ H₁ H₂ =>
      constructor
      repeat
        first
        | apply HτMap
        | apply H₀
        | apply H₁
        | apply H₂

theorem preservation_reflect :
    ∀ Γ E b τ, ctx𝔼 E -> lc b -> typing Γ (E (.reflect b)) τ -> typing Γ (.let𝕔 b (E (.code (.bvar 0)))) τ :=
  by
  intros _ _ _ _ HE Hlc Hτr
  have ⟨_, Hτr⟩ := typing𝔼 _ _ _ _ HE Hτr
  cases Hτr with
  | reflect _ _ τ Hτb =>
  constructor
  apply Hτb
  rw [open_ctx𝔼_map _ _ _ HE]; simp
  admit
  admit

theorem preservation_head𝕄 : ∀ Γ e₀ e₁ τ, head𝕄 e₀ e₁ -> lc e₀ -> typing Γ e₀ τ -> typing Γ e₁ τ :=
  by
  admit

theorem preservation : ∀ e₀ e₁ τ, step e₀ e₁ -> typing [] e₀ τ -> typing [] e₁ τ :=
  by
  intro e₀ e₁ τ Hstep
  cases Hstep with
  | step𝕄 _ _ _ HM Hlc Hhead𝕄 =>
    generalize HeqΓ : [] = Γ
    generalize HEqlvl : 0 = lvl
    have Hlength : Γ.length = lvl := by
      rw [← HeqΓ, ← HEqlvl]
      simp
    rw [HEqlvl] at HM
    clear HEqlvl
    clear HeqΓ
    induction HM generalizing τ Γ with
    | hole => apply preservation_head𝕄; apply Hhead𝕄; apply Hlc
    | cons𝔹 _ _ HB _ IHM =>
      simp; apply preservation𝔹
      apply HB
      intro; apply IHM; apply Hlength
    | consℝ _ _ HR HM IHM =>
      rw [← Hlength] at HR IHM; simp; apply preservationℝ
      apply HR
      apply lc_ctx𝕄; apply HM; apply Hlc
      intros _ _; apply IHM; rfl
  | reflect P E e HP HE Hlc =>
    generalize HeqΓ : [] = Γ
    generalize HEqlvl : 0 = lvl
    have Hlength : Γ.length = lvl := by
      rw [← HeqΓ, ← HEqlvl]
      simp
    rw [← HEqlvl]
    rw [HEqlvl] at HP
    clear HEqlvl
    clear HeqΓ
    induction HP generalizing τ Γ with
    | hole => apply preservation_reflect; apply HE; apply Hlc
    | holeℝ _ HR =>
      apply preservationℝ
      rw [Hlength]; apply HR
      apply lc_ctx𝔼; apply HE; apply Hlc
      intros _ _; apply preservation_reflect; apply HE; apply Hlc
    | cons𝔹 _ _ HB _ IHM =>
      simp; apply preservation𝔹
      apply HB
      intro; apply IHM; apply Hlength
    | consℝ _ _ HR HP IHM =>
      rw [← Hlength] at HR IHM; simp; apply preservationℝ
      apply HR
      apply lc_ctxℙ; apply HP
      apply lc_ctx𝔼; apply HE; apply Hlc
      intros _ _; apply IHM; rfl
