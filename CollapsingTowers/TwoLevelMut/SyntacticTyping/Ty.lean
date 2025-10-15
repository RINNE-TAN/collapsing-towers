import CollapsingTowers.TwoLevelMut.SyntacticTyping.Effect

inductive Ty : Type where
  | unit
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty) (φ : Effects)
  | fragment (τ : Ty)
  | rep (τ : Ty)
  | ref (τ : Ty)

@[simp]
def erase_ty : Ty → Ty
  | .unit => .unit
  | .nat => .nat
  | .arrow τa τb φ => .arrow (erase_ty τa) (erase_ty τb) (erase_effects φ)
  | .fragment τ => erase_ty τ
  | .rep τ => erase_ty τ
  | .ref τ => .ref (erase_ty τ)

@[simp]
def wbt : Stage → Ty → Prop
  | 𝟙, .nat => true
  | 𝟙, (.arrow τ𝕒 τ𝕓 _) => wbt 𝟙 τ𝕒 ∧ wbt 𝟙 τ𝕓
  | 𝟙, (.fragment τ) => wbt 𝟚 τ
  | 𝟙, .unit => true
  | 𝟙, (.ref τ) => wbt 𝟙 τ
  | 𝟙, _ => false
  | 𝟚, .nat => true
  | 𝟚, (.arrow τ𝕒 τ𝕓 φ) => wbt_effects 𝟚 φ ∧ wbt 𝟚 τ𝕒 ∧ wbt 𝟚 τ𝕓
  | 𝟚, .unit => true
  | 𝟚, (.ref τ) => wbt 𝟚 τ
  | 𝟚, _ => false
