
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.OpenClose
import CollapsingTowers.TwoLevel.SmallStep
import CollapsingTowers.TwoLevel.Env
@[simp]
def binds (x : ℕ) (τ : Ty) (Γ : TEnv) :=
  indexr x Γ = some τ

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
    typing (τ𝕒 :: Γ) (open₀ Γ.length e) (.rep τ𝕓) ->
    closed_at e Γ.length ->
    typing Γ (.let𝕔 b e) (.rep τ𝕓)

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
  | lit₂ =>
    constructor
  | lam₁ _ _ _ _ _ _ IHe
  | lam₂ _ _ _ _ _ _ IHe
  | lam𝕔 _ _ _ _ _ _ IHe =>
    apply open_closed
    apply IHe
  | app₁ _ _ _ _ _ _ _ IH₀ IH₁
  | app₂ _ _ _ _ _ _ _ IH₀ IH₁
  | plus₁ _ _ _ _ _ IH₀ IH₁
  | plus₂ _ _ _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀
    apply IH₁
  | code _ _ _ _ IH
  | reflect _ _ _ _ IH =>
    apply IH
  | lets _ _ _ _ _ _ _ _ IH₀ IH₁
  | let𝕔 _ _ _ _ _ _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀
    apply open_closed
    apply IH₁

theorem preservationℝ :
    ∀ R e₀ e₁, ctxℝ R -> (∀ Γ τ, typing Γ e₀ τ -> typing Γ e₁ τ) -> (∀ Γ τ, typing Γ (R e₀) τ -> typing Γ (R e₁) τ) :=
  by
  intro _ _ _ HR Hτe _ _ HτR
  cases HR with
  | lam𝕔 =>
    cases HτR
    constructor
    admit
    admit
  | let𝕔 => admit

theorem preservation𝔹 :
    ∀ B e₀ e₁, ctx𝔹 B -> (∀ Γ τ, typing Γ e₀ τ -> typing Γ e₁ τ) -> (∀ Γ τ, typing Γ (B e₀) τ -> typing Γ (B e₁) τ) :=
  by
  intro _ _ _ HB Hτe _ _ HτB
  cases HB
  all_goals
    cases HτB
    next H₀ H₁ H₂ =>
      constructor
      repeat
        first
        | apply Hτe
        | apply H₀
        | apply H₁
        | apply H₂

theorem preservation : ∀ Γ e₀ e₁ τ, step e₀ e₁ -> typing Γ e₀ τ -> typing Γ e₁ τ :=
  by
  intro Γ e₀ e₁ τ Hstep
  cases Hstep with
  | lets _ e v HM Hvalue =>
    induction HM generalizing Γ τ with
    | hole => admit
    | cons𝔹 _ _ HB _ IHM => simp; apply preservation𝔹; apply HB; apply IHM
    | consℝ _ _ HR _ IHM => simp; apply preservationℝ; apply HR; apply IHM
  | _ => admit
