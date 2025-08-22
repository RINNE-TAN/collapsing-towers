import CollapsingTowers.TwoLevelRec.Syntax.Defs
import CollapsingTowers.TwoLevelRec.SyntacticTyping.Env

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
      typing Γ 𝟙 e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀) φ₁ →
      typing Γ 𝟙 (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | app₁ : ∀ Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      typing Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ →
      typing Γ 𝕊 arg τ𝕒 φ₂ →
      typing Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂)
    | app₂ : ∀ Γ f arg τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ 𝟙 f (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) φ₀ →
      typing Γ 𝟙 arg (.fragment τ𝕒) φ₁ →
      typing Γ 𝟙 (.app₂ f arg) (.fragment τ𝕓) ⊤
    | lit : ∀ Γ 𝕊 n,
      typing Γ 𝕊 (.lit n) .nat ⊥
    | lift_lit : ∀ Γ n φ,
      typing Γ 𝟙 n .nat φ →
      typing Γ 𝟙 (.lift n) (.fragment .nat) ⊤
    | binary₁ : ∀ Γ 𝕊 op l r φ₀ φ₁,
      typing Γ 𝕊 l .nat φ₀ →
      typing Γ 𝕊 r .nat φ₁ →
      typing Γ 𝕊 (.binary₁ op l r) .nat (φ₀ ∪ φ₁)
    | binary₂ : ∀ Γ op l r φ₀ φ₁,
      typing Γ 𝟙 l (.fragment .nat) φ₀ →
      typing Γ 𝟙 r (.fragment .nat) φ₁ →
      typing Γ 𝟙 (.binary₂ op l r) (.fragment .nat) ⊤
    | code_fragment : ∀ Γ x τ,
      binds x (τ, 𝟚) Γ →
      wbt 𝟚 τ →
      typing Γ 𝟙 (.code (.fvar x)) (.fragment τ) ⊥
    | code_rep : ∀ Γ e τ,
      typing Γ 𝟚 e τ ⊥ →
      typing Γ 𝟙 (.code e) (.rep τ) ⊥
    | reflect : ∀ Γ e τ,
      typing Γ 𝟚 e τ ⊥ →
      typing Γ 𝟙 (.reflect e) (.fragment τ) ⊤
    | lam𝕔 : ∀ Γ e τ𝕒 τ𝕓 φ,
      typing_reification ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟙 (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | lets : ∀ Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ 𝕊 b τ𝕒 φ₀ →
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ₁ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁)
    | lets𝕔 : ∀ Γ b e τ𝕒 τ𝕓 φ,
      typing Γ 𝟚 b τ𝕒 ⊥ →
      typing_reification ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟙 (.lets𝕔 b e) (.rep τ𝕓) ⊥
    | run : ∀ Γ e τ φ,
      typing_reification Γ e (.rep τ) φ →
      closed e →
      typing Γ 𝟙 (.run e) τ ⊥
    | fix₁ : ∀ Γ 𝕊 f τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      φ₀ = φ₀ ∪ φ₁ →
      typing Γ 𝕊 f (.arrow (.arrow τ𝕒 τ𝕓 φ₀) (.arrow τ𝕒 τ𝕓 φ₀) φ₁) φ₂ →
      typing Γ 𝕊 (.fix₁ f) (.arrow τ𝕒 τ𝕓 φ₀) φ₂
    | fix₂ : ∀ Γ f τ𝕒 τ𝕓 φ,
      typing Γ 𝟙 f (.fragment (.arrow (.arrow τ𝕒 τ𝕓 ⊥) (.arrow τ𝕒 τ𝕓 ⊥) ⊥)) φ →
      typing Γ 𝟙 (.fix₂ f) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | ifz₁ : ∀ Γ 𝕊 c l r τ φ₀ φ₁ φ₂,
      typing Γ 𝕊 c .nat φ₀ →
      typing Γ 𝕊 l τ φ₁ →
      typing Γ 𝕊 r τ φ₂ →
      typing Γ 𝕊 (.ifz₁ c l r) τ (φ₀ ∪ φ₁ ∪ φ₂)
    | ifz₂ : ∀ Γ c l r τ φ₀ φ₁ φ₂,
      typing Γ 𝟙 c (.fragment .nat) φ₀ →
      typing_reification Γ l (.rep τ) φ₁ →
      typing_reification Γ r (.rep τ) φ₂ →
      typing Γ 𝟙 (.ifz₂ c l r) (.fragment τ) ⊤

  inductive typing_reification : TEnv → Expr → Ty → Effect → Prop
    | pure : ∀ Γ e τ, typing Γ 𝟙 e τ ⊥ → typing_reification Γ e τ ⊥
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
  case app₁ IHf IHarg => simp [IHf, IHarg]
  case app₂ IHf IHarg => simp [IHf, IHarg]
  case binary₁ IHl IHr => simp [IHl, IHr]
  case binary₂ IHl IHr => simp [IHl, IHr]
  case lets IHb IHe =>
    constructor; apply IHb
    rw [← lc.under_opening]; apply IHe
  case lets𝕔 IHb IHe =>
    constructor; apply IHb
    rw [← lc.under_opening]; apply IHe
  case ifz₁ IHc IHl IHr => simp [IHc, IHl, IHr]
  case ifz₂ IHc IHl IHr => simp [IHc, IHl, IHr]
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
  <;> try simp
  <;> (intros; try assumption)
  case fvar Hbinds _ =>
    simp [getr_exists_iff_index_lt_length]
    constructor; constructor; apply Hbinds
  case app₁ IHf IHarg => simp [IHf, IHarg]
  case app₂ IHf IHarg => simp [IHf, IHarg]
  case binary₁ IHl IHr => simp [IHl, IHr]
  case binary₂ IHl IHr => simp [IHl, IHr]
  case code_fragment Hbinds _ =>
    simp [getr_exists_iff_index_lt_length]
    constructor; constructor; apply Hbinds
  case lets Hclosed IHb _ =>
    constructor; apply IHb; apply Hclosed
  case lets𝕔 Hclosed IHb _ =>
    constructor; apply IHb; apply Hclosed
  case ifz₁ IHc IHl IHr => simp [IHc, IHl, IHr]
  case ifz₂ IHc IHl IHr => simp [IHc, IHl, IHr]
  apply Hτ

lemma typing_reification.closed_at_env : ∀ Γ e τ φ, typing_reification Γ e τ φ → closed_at e Γ.length :=
  by
  intros Γ e τ φ Hτ
  cases Hτ <;> (apply typing.closed_at_env; assumption)

lemma typing.wf : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → wf_at e Γ.length :=
  by
  intros Γ 𝕊 e τ φ Hτ
  constructor
  apply typing.regular; apply Hτ
  apply typing.closed_at_env; apply Hτ

lemma typing_reification.wf : ∀ Γ e τ φ, typing_reification Γ e τ φ → wf_at e Γ.length :=
  by
  intros Γ e τ φ Hτ
  cases Hτ <;> (apply typing.wf; assumption)

lemma typing.dynamic_impl_pure : ∀ Γ e τ φ, typing Γ 𝟚 e τ φ → wbt 𝟚 τ ∧ φ = ⊥ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec
    (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → wbt 𝕊 τ ∧ φ = ⊥)
    (fun Γ e τ φ (H : typing_reification Γ e τ φ) => true)
  <;> intros
  <;> (try assumption)
  <;> (try contradiction)
  case fvar x _ Hbinds Hwbt HEq𝕊 =>
    constructor; apply Hwbt; rfl
  case lam Hwbt₀ Hclose IH HEq𝕊 =>
    have ⟨Hwbt₁, Hφ₀⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt₀ Hwbt₁
    constructor
    . constructor
      apply Hφ₀; constructor
      apply Hwbt₀; apply Hwbt₁
    . rfl
  case app₁ IHf IHarg HEq𝕊 =>
    have ⟨Hwbt₁, Hφ₁⟩ := IHf HEq𝕊
    have ⟨Hwbt₂, Hφ₂⟩ := IHarg HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt₁ Hwbt₂
    constructor
    . apply Hwbt₁.right.right
    . simp [Hφ₁, Hφ₂, Hwbt₁.left]
  case lit HEq𝕊 =>
    rw [← HEq𝕊]
    constructor
    . simp
    . rfl
  case binary₁ IHl IHr HEq𝕊 =>
    have ⟨Hwbt₀, Hφ₀⟩ := IHl HEq𝕊
    have ⟨Hwbt₁, Hφ₁⟩ := IHr HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt₀ Hwbt₁
    constructor
    . simp
    . simp [Hφ₀, Hφ₁]
  case lets Hwbt Hclose IHb IHe HEq𝕊 =>
    have ⟨Hwbt₀, Hφ₀⟩ := IHb HEq𝕊
    have ⟨Hwbt₁, Hφ₁⟩ := IHe HEq𝕊
    constructor
    . apply Hwbt₁
    . simp [Hφ₀, Hφ₁]
  case fix₁ IHf HEq𝕊 =>
    have ⟨Hwbt, Hφ⟩ := IHf HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt
    constructor
    . apply Hwbt.right.left
    . simp [Hφ]
  case ifz₁ IHc IHl IHr HEq𝕊 =>
    have ⟨Hwbt₀, Hφ₀⟩ := IHc HEq𝕊
    have ⟨Hwbt₁, Hφ₁⟩ := IHl HEq𝕊
    have ⟨Hwbt₂, Hφ₂⟩ := IHr HEq𝕊
    constructor
    . apply Hwbt₂
    . simp [Hφ₀, Hφ₁, Hφ₂]
  case pure => simp
  case reify => simp

lemma typing.dynamic_impl_grounded : ∀ Γ e τ φ, typing Γ 𝟚 e τ φ → grounded e :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec
    (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → grounded e)
    (fun Γ e τ φ (H : typing_reification Γ e τ φ) => true)
  <;> intros
  <;> (try assumption)
  <;> (try contradiction)
  <;> simp
  case lam IH HEq𝕊 =>
    rw [grounded.under_opening]; apply IH; apply HEq𝕊
  case app₁ IH₀ IH₁ HEq𝕊 =>
    constructor
    apply IH₀; apply HEq𝕊
    apply IH₁; apply HEq𝕊
  case binary₁ IH₀ IH₁ HEq𝕊 =>
    constructor
    apply IH₀; apply HEq𝕊
    apply IH₁; apply HEq𝕊
  case lets IH₀ IH₁ HEq𝕊 =>
    constructor
    apply IH₀; apply HEq𝕊
    rw [grounded.under_opening]; apply IH₁; apply HEq𝕊
  case fix₁ IH HEq𝕊 =>
    apply IH; apply HEq𝕊
  case ifz₁ IH₀ IH₁ IH₂ HEq𝕊 =>
    constructor
    apply IH₀; apply HEq𝕊; constructor
    apply IH₁; apply HEq𝕊
    apply IH₂; apply HEq𝕊

lemma typing_reification.under_code :
  ∀ Γ e τ φ,
    typing_reification Γ (.code e) (.rep τ) φ →
    typing Γ 𝟚 e τ ⊥ :=
  by
  intros Γ e τ φ Hτ
  cases Hτ
  case pure Hτ =>
    cases Hτ
    case code_rep Hτ => apply Hτ
  case reify Hτ =>
    cases Hτ
    case code_fragment Hwbt Hbinds =>
      apply typing.fvar; apply Hbinds; apply Hwbt
