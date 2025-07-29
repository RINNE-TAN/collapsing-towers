import CollapsingTowers.TwoLvLBasic.Syntax.Defs
import CollapsingTowers.TwoLvLBasic.Utils.Defs
import CollapsingTowers.TwoLvLBasic.Semantic.Defs
@[simp]
def wbt : Stage → Ty → Prop
  | 𝟙, .nat => true
  | 𝟙, (.arrow τ𝕒 τ𝕓 _) => wbt 𝟙 τ𝕒 ∧ wbt 𝟙 τ𝕓
  | 𝟙, (.fragment τ) => wbt 𝟚 τ
  | 𝟙, _ => false
  | 𝟚, .nat => true
  | 𝟚, (.arrow τ𝕒 τ𝕓 φ) => φ = ∅ ∧ wbt 𝟚 τ𝕒 ∧ wbt 𝟚 τ𝕓
  | 𝟚, _ => false

lemma wbt.escape : ∀ 𝕊 τ, wbt 𝕊 τ → wbt 𝟙 τ :=
  by
  intros 𝕊 τ Hwbt
  cases 𝕊
  case stat => assumption
  case dyn =>
    induction τ with
    | nat => simp
    | arrow _ _ _ IH₀ IH₁ =>
      constructor
      apply IH₀; apply Hwbt.right.left
      apply IH₁; apply Hwbt.right.right
    | fragment => nomatch Hwbt
    | rep => nomatch Hwbt

mutual
  inductive typing : TEnv → Stage → Expr → Ty → Effect → Prop where
    | fvar : ∀ Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      wbt 𝕊 τ →
      typing Γ 𝕊 (.fvar x) τ ∅
    | lam : ∀ Γ 𝕊 e τ𝕒 τ𝕓 φ,
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lam e) (.arrow τ𝕒 τ𝕓 φ) ∅
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
    | lam𝕔 : ∀ Γ e τ𝕒 τ𝕓 φ,
      typing_reification ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟙 (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ∅)) .reify
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

lemma typing.regular : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → lc e :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => lc e)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => lc e)
  <;> try simp
  <;> intros
  case lam IH =>
    rw [← lc.under_opening]; apply IH
  case lam𝕔 IH =>
    rw [← lc.under_opening]; apply IH
  case app₁ IHf IHarg =>
    constructor; apply IHf; apply IHarg
  case app₂ IHf IHarg =>
    constructor; apply IHf; apply IHarg
  case lets IHb IHe =>
    constructor; apply IHb
    rw [← lc.under_opening]; apply IHe
  case lets𝕔 IHb IHe =>
    constructor; apply IHb
    rw [← lc.under_opening]; apply IHe
  apply Hτ

lemma typing_reification.regular : ∀ Γ e τ φ, typing_reification Γ e τ φ → lc e :=
  by
  intros Γ e τ φ Hτ
  cases Hτ <;> (apply typing.regular; assumption)

lemma typing.closed_at_env : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → closed_at e Γ.length :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => closed_at e Γ.length)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => closed_at e Γ.length)
  <;> (intros; try assumption)
  case fvar Hbinds _ =>
    simp [getr_exists_iff_index_lt_length]
    constructor; constructor
    apply Hbinds
  case app₁ IHf IHarg =>
    constructor; apply IHf; apply IHarg
  case app₂ IHf IHarg =>
    constructor; apply IHf; apply IHarg
  case lit => simp
  case code_fragment Hbinds _ =>
    simp [getr_exists_iff_index_lt_length]
    constructor; constructor
    apply Hbinds
  case lets Hclose IHb _ =>
    constructor; apply IHb; apply Hclose
  case lets𝕔 Hclose IHb _ =>
    constructor; apply IHb; apply Hclose

lemma typing_reification.closed_at_env : ∀ Γ e τ φ, typing_reification Γ e τ φ → closed_at e Γ.length :=
  by
  intros Γ e τ φ Hτ
  cases Hτ
  all_goals
    next Hτ =>
      apply typing.closed_at_env
      apply Hτ

lemma typing.dyn_impl_pure : ∀ Γ e τ φ, typing Γ 𝟚 e τ φ → wbt 𝟚 τ ∧ φ = ∅ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec
    (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → wbt 𝕊 τ ∧ φ = ∅)
    (fun Γ e τ φ (H : typing_reification Γ e τ φ) => true)
  <;> (try intros; assumption)
  <;> (try intros; contradiction)
  case fvar =>
    intros _ _ x _ Hbinds HwellBinds HEq𝕊
    constructor; apply HwellBinds; rfl
  case lam =>
    intros _ _ _ _ _ _ _ HwellBinds₀ Hclose IH HEq𝕊
    have ⟨HwellBinds₁, Hφ₀⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at HwellBinds₀ HwellBinds₁
    constructor
    . constructor
      apply Hφ₀; constructor
      apply HwellBinds₀; apply HwellBinds₁
    . rfl
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg HEq𝕊
    have ⟨HwellBinds₁, Hφ₁⟩ := IHf HEq𝕊
    have ⟨HwellBinds₂, Hφ₂⟩ := IHarg HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at HwellBinds₁ HwellBinds₂
    constructor
    . apply HwellBinds₁.right.right
    . rw [Hφ₁, Hφ₂, HwellBinds₁.left]; rfl
  case lit =>
    intros _ _ _ HEq𝕊
    rw [← HEq𝕊]
    constructor
    . simp
    . rfl
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe HEq𝕊
    have ⟨HwellBinds₁, Hφ₁⟩ := IHb HEq𝕊
    have ⟨HwellBinds₂, Hφ₂⟩ := IHe HEq𝕊
    constructor
    . apply HwellBinds₂
    . rw [Hφ₁, Hφ₂]; rfl
  case pure => simp
  case reify => simp

lemma typing.rep_ty_iff_value_code :
  ∀ v τ φ,
    value v →
    typing_reification [] v (.rep τ) φ →
    ∃ e, v = .code e ∧ typing [] 𝟚 e τ ∅ :=
  by
  intros v τ φ Hvalue Hτ
  cases Hvalue
  case code e _ =>
    exists e; simp
    cases Hτ
    case pure Hτ => cases Hτ; assumption
    case reify Hτ => nomatch Hτ
  all_goals
  next =>
    cases Hτ <;> next Hτ => nomatch Hτ
