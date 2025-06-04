
import CollapsingTowers.TwoLevelPCP.Syntax
import CollapsingTowers.TwoLevelPCP.SmallStep
import CollapsingTowers.TwoLevelPCP.Env
inductive typing : Stage → TEnv → Expr → Ty → Prop where
  | fvar : ∀ 𝕊 Γ x τ,
    binds x τ 𝕊 Γ →
    typing 𝕊 Γ (.fvar x) τ
  | lam₁ : ∀ 𝕊 Γ e τ𝕒 τ𝕓,
    typing 𝕊 ((τ𝕒, 𝕊) :: Γ) (open₀ Γ.length e) τ𝕓 →
    binding_time 𝕊 τ𝕒 →
    closed_at e Γ.length →
    typing 𝕊 Γ (.lam₁ e) (.arrow τ𝕒 τ𝕓)
  | lift_lam : ∀ Γ e τ𝕒 τ𝕓,
    typing .fst Γ e (.arrow (.rep₁ τ𝕒) (.rep₁ τ𝕓)) →
    typing .fst Γ (.lift e) (.rep₁ (.arrow τ𝕒 τ𝕓))
  | app₁ : ∀ 𝕊 Γ f arg τ𝕒 τ𝕓,
    typing 𝕊 Γ f (.arrow τ𝕒 τ𝕓) →
    typing 𝕊 Γ arg τ𝕒 →
    typing 𝕊 Γ (.app₁ f arg) τ𝕓
  | app₂ : ∀ Γ f arg τ𝕒 τ𝕓,
    typing .fst Γ f (.rep₁ (.arrow τ𝕒 τ𝕓)) →
    typing .fst Γ arg (.rep₁ τ𝕒) →
    typing .fst Γ (.app₂ f arg) (.rep₁ τ𝕓)
  | plus₁ : ∀ 𝕊 Γ l r,
    typing 𝕊 Γ l .nat →
    typing 𝕊 Γ r .nat →
    typing 𝕊 Γ (.plus₁ l r) .nat
  | plus₂ : ∀ Γ l r,
    typing .fst Γ l (.rep₁ .nat) →
    typing .fst Γ r (.rep₁ .nat) →
    typing .fst Γ (.plus₂ l r) (.rep₁ .nat)
  | lit₁ : ∀ 𝕊 Γ n,
    typing 𝕊 Γ (.lit₁ n) .nat
  | lift_lit : ∀ Γ n,
    typing .fst Γ n .nat →
    typing .fst Γ (.lift n) (.rep₁ .nat)
  | code₁ : ∀ Γ x τ,
    binds x τ .snd Γ →
    typing .fst Γ (.code (.fvar x)) (.rep₁ τ)
  | code₂ : ∀ Γ e τ,
    typing .snd Γ e τ →
    typing .fst Γ (.code e) (.rep₂ τ)
  | lift_code : ∀ Γ e τ,
    typing .fst Γ e (.rep₁ τ) →
    typing .fst Γ e (.rep₂ τ)
  | reflect : ∀ Γ e τ,
    typing .snd Γ e τ →
    typing .fst Γ (.reflect e) (.rep₁ τ)
  | lam𝕔 : ∀ Γ e τ𝕒 τ𝕓,
    typing .fst ((τ𝕒, .snd) :: Γ) (open₀ Γ.length e) (.rep₂ τ𝕓) →
    binding_time .snd τ𝕒 →
    closed_at e Γ.length →
    typing .fst Γ (.lam𝕔 e) (.rep₁ (.arrow τ𝕒 τ𝕓))
  | lets : ∀ 𝕊 Γ b e τ𝕒 τ𝕓,
    typing 𝕊 Γ b τ𝕒 →
    typing 𝕊 ((τ𝕒, 𝕊) :: Γ) (open₀ Γ.length e) τ𝕓 →
    binding_time 𝕊 τ𝕒 →
    closed_at e Γ.length →
    typing 𝕊 Γ (.lets b e) τ𝕓
  | let𝕔 : ∀ Γ b e τ𝕒 τ𝕓,
    typing .snd Γ b τ𝕒 →
    typing .fst ((τ𝕒, .snd) :: Γ) (open₀ Γ.length e) τ𝕓 →
    binding_time .snd τ𝕒 →
    closed_at e Γ.length →
    typing .fst Γ (.let𝕔 b e) τ𝕓
