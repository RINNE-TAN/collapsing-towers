import CollapsingTowers.TwoLevelRec.Syntax.Defs
import CollapsingTowers.TwoLevelRec.SyntacticTyping.Ty
import CollapsingTowers.TwoLevelRec.Utils.Defs

inductive Stage : Type where
  | stat
  | dyn

notation:max "𝟙" => Stage.stat

notation:max "𝟚" => Stage.dyn

@[simp]
def wbt : Stage → Ty → Prop
  | 𝟙, .nat => true
  | 𝟙, (.arrow τ𝕒 τ𝕓 φ) => φ = ⊥ ∧ wbt 𝟙 τ𝕒 ∧ wbt 𝟙 τ𝕓
  | 𝟙, _ => false
  | 𝟚, .nat => true
  | 𝟚, (.arrow τ𝕒 τ𝕓 _) => wbt 𝟚 τ𝕒 ∧ wbt 𝟚 τ𝕓
  | 𝟚, (.fragment τ) => wbt 𝟙 τ
  | 𝟚, _ => false

lemma wbt.escape : ∀ 𝕊 τ, wbt 𝕊 τ → wbt 𝟚 τ :=
  by
  intros 𝕊 τ Hwbt
  cases 𝕊
  case stat =>
    induction τ with
    | nat => simp
    | arrow _ _ _ IH₀ IH₁ =>
      constructor
      apply IH₀; apply Hwbt.right.left
      apply IH₁; apply Hwbt.right.right
    | fragment => nomatch Hwbt
    | rep => nomatch Hwbt
  case dyn => assumption

abbrev TEnv :=
  List (Ty × Stage)

notation:max "⦰" => ([] : TEnv)

mutual
  inductive typing : TEnv → Stage → Expr → Ty → Effect → Prop where
    | fvar : ∀ Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      wbt 𝕊 τ →
      typing Γ 𝕊 (.fvar x) τ ⊥
    | lam : ∀ Γ 𝕊 e τ𝕒 τ𝕓 φ,
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lam e) (.arrow τ𝕒 τ𝕓 φ) ⊥
    | lift_lam : ∀ Γ e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ 𝟚 e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀) φ₁ →
      typing Γ 𝟚 (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | app₁ : ∀ Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      typing Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ →
      typing Γ 𝕊 arg τ𝕒 φ₂ →
      typing Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂)
    | app₂ : ∀ Γ f arg τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ 𝟚 f (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) φ₀ →
      typing Γ 𝟚 arg (.fragment τ𝕒) φ₁ →
      typing Γ 𝟚 (.app₂ f arg) (.fragment τ𝕓) ⊤
    | binary₁ : ∀ Γ 𝕊 op l r φ₀ φ₁,
      typing Γ 𝕊 l .nat φ₀ →
      typing Γ 𝕊 r .nat φ₁ →
      typing Γ 𝕊 (.binary₁ op l r) .nat (φ₀ ∪ φ₁)
    | binary₂ : ∀ Γ op l r φ₀ φ₁,
      typing Γ 𝟚 l (.fragment .nat) φ₀ →
      typing Γ 𝟚 r (.fragment .nat) φ₁ →
      typing Γ 𝟚 (.binary₂ op l r) (.fragment .nat) ⊤
    | lit : ∀ Γ 𝕊 n,
      typing Γ 𝕊 (.lit n) .nat ⊥
    | lift_lit : ∀ Γ n φ,
      typing Γ 𝟚 n .nat φ →
      typing Γ 𝟚 (.lift n) (.fragment .nat) ⊤
    | code_fragment : ∀ Γ x τ,
      binds x (τ, 𝟙) Γ →
      wbt 𝟙 τ →
      typing Γ 𝟚 (.code (.fvar x)) (.fragment τ) ⊥
    | code_rep : ∀ Γ e τ,
      typing Γ 𝟙 e τ ⊥ →
      typing Γ 𝟚 (.code e) (.rep τ) ⊥
    | reflect : ∀ Γ e τ,
      typing Γ 𝟙 e τ ⊥ →
      typing Γ 𝟚 (.reflect e) (.fragment τ) ⊤
    | lam𝕔 : ∀ Γ e τ𝕒 τ𝕓 φ,
      typing_reification ((τ𝕒, 𝟙) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟙 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟚 (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | lets : ∀ Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ 𝕊 b τ𝕒 φ₀ →
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ₁ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁)
    | lets𝕔 : ∀ Γ b e τ𝕒 τ𝕓 φ,
      typing Γ 𝟙 b τ𝕒 ⊥ →
      typing_reification ((τ𝕒, 𝟙) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟙 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟚 (.lets𝕔 b e) (.rep τ𝕓) ⊥
    | run : ∀ Γ e τ φ,
      typing_reification Γ e (.rep τ) φ →
      closed e →
      typing Γ 𝟚 (.run e) τ ⊥
    | fix₁ : ∀ Γ 𝕊 f τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      φ₀ = φ₀ ∪ φ₁ →
      typing Γ 𝕊 f (.arrow (.arrow τ𝕒 τ𝕓 φ₀) (.arrow τ𝕒 τ𝕓 φ₀) φ₁) φ₂ →
      typing Γ 𝕊 (.fix₁ f) (.arrow τ𝕒 τ𝕓 φ₀) φ₂
    | fix₂ : ∀ Γ f τ𝕒 τ𝕓 φ,
      typing Γ 𝟚 f (.fragment (.arrow (.arrow τ𝕒 τ𝕓 ⊥) (.arrow τ𝕒 τ𝕓 ⊥) ⊥)) φ →
      typing Γ 𝟚 (.fix₂ f) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | ifz₁ : ∀ Γ 𝕊 c l r τ φ₀ φ₁ φ₂,
      typing Γ 𝕊 c .nat φ₀ →
      typing Γ 𝕊 l τ φ₁ →
      typing Γ 𝕊 r τ φ₁ →
      typing Γ 𝕊 (.ifz₁ c l r) τ (φ₀ ∪ φ₁ ∪ φ₂)
    | ifz₂ : ∀ Γ c l r τ φ₀ φ₁ φ₂,
      typing Γ 𝟚 c (.fragment .nat) φ₀ →
      typing_reification Γ l (.rep τ) φ₁ →
      typing_reification Γ r (.rep τ) φ₂ →
      typing Γ 𝟚 (.ifz₂ c l r) (.fragment τ) ⊤

  inductive typing_reification : TEnv → Expr → Ty → Effect → Prop
    | pure : ∀ Γ e τ, typing Γ 𝟚 e τ ⊥ → typing_reification Γ e τ ⊥
    | reify : ∀ Γ e τ φ, typing Γ 𝟚 e (.fragment τ) φ → typing_reification Γ e (.rep τ) φ
end
