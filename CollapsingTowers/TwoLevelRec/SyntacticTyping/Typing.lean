import CollapsingTowers.TwoLevelRec.Syntax.Defs
import CollapsingTowers.TwoLevelRec.Utils.Defs
import CollapsingTowers.TwoLevelRec.Semantic.Defs
@[simp]
def wbt : Stage → Ty → Prop
  | 𝟙, .nat => true
  | 𝟙, (.arrow τ𝕒 τ𝕓 _) => wbt 𝟙 τ𝕒 ∧ wbt 𝟙 τ𝕓
  | 𝟙, (.fragment τ) => wbt 𝟚 τ
  | 𝟙, _ => false
  | 𝟚, .nat => true
  | 𝟚, (.arrow τ𝕒 τ𝕓 φ) => φ = ∅ ∧ wbt 𝟚 τ𝕒 ∧ wbt 𝟚 τ𝕓
  | 𝟚, _ => false

mutual
  inductive typing : TEnv → Stage → Expr → Ty → Effect → Prop where
    | fvar : ∀ Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      wbt 𝕊 τ →
      typing Γ 𝕊 (.fvar x) τ ∅
    | fix : ∀ Γ 𝕊 e τ𝕒 τ𝕓 φ,
      -- x ↦ τ𝕒, f ↦ τ𝕒 → τ𝕓, Γ ⊢ e : τ𝕓
      -- —————————————————————————————————
      -- Γ ⊢ fix e : τ𝕒 → τ𝕓
      typing ((τ𝕒, 𝕊) :: (.arrow τ𝕒 τ𝕓 φ, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length}{1 ↦ Γ.length + 1} e) τ𝕓 φ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.fix e) (.arrow τ𝕒 τ𝕓 φ) ∅
    | lift_lam : ∀ Γ e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ 𝟙 e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀) φ₁ →
      typing Γ 𝟙 (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ∅)) .reify
    | app₁ : ∀ Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      typing Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ →
      typing Γ 𝕊 arg τ𝕒 φ₂ →
      typing Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂)
    | app₂ : ∀ Γ f arg τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ 𝟙 f (.fragment (.arrow τ𝕒 τ𝕓 ∅)) φ₀ →
      typing Γ 𝟙 arg (.fragment τ𝕒) φ₁ →
      typing Γ 𝟙 (.app₂ f arg) (.fragment τ𝕓) .reify
    | lit : ∀ Γ 𝕊 n,
      typing Γ 𝕊 (.lit n) .nat ∅
    | lift_lit : ∀ Γ n φ,
      typing Γ 𝟙 n .nat φ →
      typing Γ 𝟙 (.lift n) (.fragment .nat) .reify
    | code_fragment : ∀ Γ x τ,
      binds x (τ, 𝟚) Γ →
      wbt 𝟚 τ →
      typing Γ 𝟙 (.code (.fvar x)) (.fragment τ) ∅
    | code_rep : ∀ Γ e τ,
      typing Γ 𝟚 e τ ∅ →
      typing Γ 𝟙 (.code e) (.rep τ) ∅
    | reflect : ∀ Γ e τ,
      typing Γ 𝟚 e τ ∅ →
      typing Γ 𝟙 (.reflect e) (.fragment τ) .reify
    | fix𝕔 : ∀ Γ e τ𝕒 τ𝕓 φ,
      -- x ↦ τ𝕒, f ↦ τ𝕒 → τ𝕓, Γ ⊢ e : <τ𝕓>
      -- —————————————————————————————————
      -- Γ ⊢ fix e : <τ𝕒 → τ𝕓>
      typing_reification ((τ𝕒, 𝟚) :: (.arrow τ𝕒 τ𝕓 ∅, 𝟚) :: Γ) ({0 ↦ Γ.length}{1 ↦ Γ.length + 1} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟙 (.fix𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ∅)) .reify
    | lets : ∀ Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ 𝕊 b τ𝕒 φ₀ →
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ₁ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁)
    | lets𝕔 : ∀ Γ b e τ𝕒 τ𝕓 φ,
      typing Γ 𝟚 b τ𝕒 ∅ →
      typing_reification ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟙 (.lets𝕔 b e) (.rep τ𝕓) ∅
    | run : ∀ Γ e τ φ,
      typing_reification Γ e (.rep τ) φ →
      closed e →
      typing Γ 𝟙 (.run e) τ ∅

  inductive typing_reification : TEnv → Expr → Ty → Effect → Prop
    | pure : ∀ Γ e τ, typing Γ 𝟙 e τ ∅ → typing_reification Γ e τ ∅
    | reify : ∀ Γ e τ φ, typing Γ 𝟙 e (.fragment τ) φ → typing_reification Γ e (.rep τ) φ
end
