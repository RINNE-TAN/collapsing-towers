import CollapsingTowers.TwoLevelBasic.SyntacticTyping.Effect

inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty) (φ : Effect)
  | fragment (τ : Ty)
  | rep (τ : Ty)

@[simp]
def erase_ty : Ty → Ty
  | .nat => .nat
  | .arrow τa τb _ => .arrow (erase_ty τa) (erase_ty τb) ⊥
  | .fragment τ => erase_ty τ
  | .rep τ => erase_ty τ

inductive Stage : Type where
  | static
  | dynamic

notation:max "𝟙" => Stage.static

notation:max "𝟚" => Stage.dynamic

@[simp]
def wbt : Stage → Ty → Prop
  | 𝟙, .nat => true
  | 𝟙, (.arrow τ𝕒 τ𝕓 _) => wbt 𝟙 τ𝕒 ∧ wbt 𝟙 τ𝕓
  | 𝟙, (.fragment τ) => wbt 𝟚 τ
  | 𝟙, _ => false
  | 𝟚, .nat => true
  | 𝟚, (.arrow τ𝕒 τ𝕓 φ) => φ = ⊥ ∧ wbt 𝟚 τ𝕒 ∧ wbt 𝟚 τ𝕓
  | 𝟚, _ => false

lemma wbt.escape : ∀ τ, wbt 𝟚 τ → wbt 𝟙 τ :=
  by
  intros τ Hwbt
  induction τ with
  | nat => simp
  | arrow _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hwbt.right.left
    apply IH₁; apply Hwbt.right.right
  | fragment => nomatch Hwbt
  | rep => nomatch Hwbt

lemma grounded_ty.under_erase : ∀ τ, wbt 𝟚 (erase_ty τ) :=
  by
  intros τ
  induction τ
  case nat => simp
  case arrow IH₀ IH₁ =>
    constructor; rfl
    constructor; apply IH₀; apply IH₁
  case fragment IH => apply IH
  case rep IH => apply IH

lemma erasable.fragment : ∀ τ₀ τ₁, erase_ty τ₀ ≠ .fragment τ₁ :=
  by
  intros τ₀ τ₁
  induction τ₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.rep : ∀ τ₀ τ₁, erase_ty τ₀ ≠ .rep τ₁ :=
  by
  intros τ₀ τ₁
  induction τ₀ <;> simp
  all_goals next IH => apply IH

lemma grounded_ty_iff_erase_identity : ∀ τ, wbt 𝟚 τ ↔ erase_ty τ = τ :=
  by
  intros τ
  induction τ
  case nat => simp
  case arrow IH𝕒 IH𝕓 =>
    simp [IH𝕒, IH𝕓]
    constructor
    . intros H; simp [H]
    . intros H; simp [H]
  case fragment => simp; apply erasable.fragment
  case rep => simp; apply erasable.rep
