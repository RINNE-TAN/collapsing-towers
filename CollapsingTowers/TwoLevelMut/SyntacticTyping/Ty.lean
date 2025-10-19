import CollapsingTowers.TwoLevelMut.SyntacticTyping.Effect

inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty) (φ : REffects) (ω : MEffects)
  | fragment (τ : Ty)
  | rep (τ : Ty)
  | unit
  | ref (τ : Ty)

@[simp]
def erase_ty : Ty → Ty
  | .nat => .nat
  | .arrow τa τb _ ω => .arrow (erase_ty τa) (erase_ty τb) ⊥ (erase_meffects ω)
  | .fragment τ => erase_ty τ
  | .rep τ => erase_ty τ
  | .unit => .unit
  | .ref τ => .ref (erase_ty τ)

@[simp]
def escape_ty : Ty → Ty
  | .nat => .nat
  | .arrow τa τb φ ω => .arrow (escape_ty τa) (escape_ty τb) φ (escape_meffects ω)
  | .fragment τ => .fragment (escape_ty τ)
  | .rep τ => .rep (escape_ty τ)
  | .unit => .unit
  | .ref τ => .ref (escape_ty τ)

@[simp]
def wbt : Stage → Ty → Prop
  | 𝟙, .nat => true
  | 𝟙, (.arrow τ𝕒 τ𝕓 _ _) => wbt 𝟙 τ𝕒 ∧ wbt 𝟙 τ𝕓
  | 𝟙, (.fragment τ) => wbt 𝟚 τ
  | 𝟙, .unit => true
  | 𝟙, (.ref τ) => wbt 𝟙 τ
  | 𝟙, _ => false
  | 𝟚, .nat => true
  | 𝟚, (.arrow τ𝕒 τ𝕓 φ ω) => φ = ⊥ ∧ wbt_meffects 𝟚 ω ∧ wbt 𝟚 τ𝕒 ∧ wbt 𝟚 τ𝕓
  | 𝟚, .unit => true
  | 𝟚, (.ref τ) => wbt 𝟚 τ
  | 𝟚, _ => false

lemma wbt.escape : ∀ τ, wbt 𝟚 τ → wbt 𝟙 (escape_ty τ) :=
  by
  intros τ Hwbt
  induction τ
  case nat => simp
  case arrow IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hwbt.right.right.left
    apply IH₁; apply Hwbt.right.right.right
  case fragment => nomatch Hwbt
  case rep => nomatch Hwbt
  case unit => simp
  case ref IH => apply IH; apply Hwbt

lemma grounded_ty.under_erase : ∀ τ, wbt 𝟚 (erase_ty τ) :=
  by
  intros τ
  induction τ
  case nat => simp
  case arrow IH₀ IH₁ =>
    constructor; rfl
    constructor; apply grounded_meffects.under_erase
    simp [IH₀, IH₁]
  case fragment IH => simp [IH]
  case rep IH => simp [IH]
  case unit => simp
  case ref IH => simp [IH]

@[simp]
lemma erase_ty.cancel_escape : ∀ τ, erase_ty (escape_ty τ) = erase_ty τ :=
  by
  intros τ
  induction τ
  case nat => simp
  case arrow IH₀ IH₁ =>
    rw [escape_ty, erase_ty, erase_meffects.cancel_escape]
    simp [IH₀, IH₁]
  case fragment IH => simp [IH]
  case rep IH => simp [IH]
  case unit => simp
  case ref IH => simp [IH]
