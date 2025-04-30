
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
    Γ.length ∉ fv e ->
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
  repeat simp

example : typing [] expr₂ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₂, x₀]
  repeat constructor
  repeat simp

example : typing [] expr₃ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₃, x₀, x₁]
  repeat constructor
  repeat simp

example : typing [] expr₄ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₄, x₀, x₁]
  repeat constructor
  repeat simp

example : typing [] expr₅ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₅, x₀, x₁, x₂]
  repeat constructor
  repeat simp

example : typing [] expr₆ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₆, x₀, x₁, x₂]
  repeat constructor
  repeat simp

example : typing [] expr₇ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₇, x₀, x₁, x₂]
  repeat constructor
  repeat simp

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
