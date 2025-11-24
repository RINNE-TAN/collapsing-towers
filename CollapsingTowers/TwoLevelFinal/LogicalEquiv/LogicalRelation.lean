import CollapsingTowers.TwoLevelFinal.SyntacticSoundness.Defs
import CollapsingTowers.TwoLevelFinal.LogicalEquiv.World

-- (σ₀, σ₁) : 𝓦 ≜ ∀ 𝓦(l₀, l₁). σ₀(l₁) = σ₀(l₁)
@[simp]
def log_well_store (𝓦 : World) (σ₀ σ₁ : Store) : Prop :=
  PartialBijection 𝓦 ∧ (
  ∀ l₀ l₁,
    𝓦 l₀ l₁ →
    ∃ n,
      binds l₀ (.lit n) σ₀ ∧
      binds l₁ (.lit n) σ₁
  )

abbrev KripkeWorld := Nat × World

@[simp]
def KripkeWorld.future : KripkeWorld → KripkeWorld → Prop :=
  fun (k, 𝓦₀) (j, 𝓦₁) => j ≤ k ∧ 𝓦₁ ⊒ 𝓦₀

notation:max 𝓦₁ " ⊇ " 𝓦₀  => KripkeWorld.future 𝓦₀ 𝓦₁
