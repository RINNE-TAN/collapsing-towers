import Instar.TwoLevelRec.Syntax.Defs
import Instar.TwoLevelRec.SyntacticTyping.Env
import Instar.TwoLevelRec.OperationalSemantics.Defs

mutual
  inductive typing : TEnv → Stage → Expr → Ty → Effect → Prop where
    | fvar : ∀ Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      wbt 𝕊 τ →
      typing Γ 𝕊 (.fvar x) τ ⊥
    | lam : ∀ Γ 𝕊 e τ𝕒 τ𝕓 ε,
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 ε →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lam e) (.arrow τ𝕒 τ𝕓 ε) ⊥
    | lift_lam : ∀ Γ e τ𝕒 τ𝕓 ε₀ ε₁,
      typing Γ 𝟙 e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) ε₀) ε₁ →
      typing Γ 𝟙 (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | app₁ : ∀ Γ 𝕊 f arg τ𝕒 τ𝕓 ε₀ ε₁ ε₂,
      typing Γ 𝕊 f (.arrow τ𝕒 τ𝕓 ε₀) ε₁ →
      typing Γ 𝕊 arg τ𝕒 ε₂ →
      typing Γ 𝕊 (.app₁ f arg) τ𝕓 (ε₀ ∪ ε₁ ∪ ε₂)
    | app₂ : ∀ Γ f arg τ𝕒 τ𝕓 ε₀ ε₁,
      typing Γ 𝟙 f (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ε₀ →
      typing Γ 𝟙 arg (.fragment τ𝕒) ε₁ →
      typing Γ 𝟙 (.app₂ f arg) (.fragment τ𝕓) ⊤
    | lit : ∀ Γ 𝕊 n,
      typing Γ 𝕊 (.lit n) .nat ⊥
    | lift_lit : ∀ Γ n ε,
      typing Γ 𝟙 n .nat ε →
      typing Γ 𝟙 (.lift n) (.fragment .nat) ⊤
    | binary₁ : ∀ Γ 𝕊 op l r ε₀ ε₁,
      typing Γ 𝕊 l .nat ε₀ →
      typing Γ 𝕊 r .nat ε₁ →
      typing Γ 𝕊 (.binary₁ op l r) .nat (ε₀ ∪ ε₁)
    | binary₂ : ∀ Γ op l r ε₀ ε₁,
      typing Γ 𝟙 l (.fragment .nat) ε₀ →
      typing Γ 𝟙 r (.fragment .nat) ε₁ →
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
    | lam𝕔 : ∀ Γ e τ𝕒 τ𝕓 ε,
      typing_reification ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) ε →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟙 (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | lets : ∀ Γ 𝕊 b e τ𝕒 τ𝕓 ε₀ ε₁,
      typing Γ 𝕊 b τ𝕒 ε₀ →
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 ε₁ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lets b e) τ𝕓 (ε₀ ∪ ε₁)
    | lets𝕔 : ∀ Γ b e τ𝕒 τ𝕓 ε,
      typing Γ 𝟚 b τ𝕒 ⊥ →
      typing_reification ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) ε →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟙 (.lets𝕔 b e) (.rep τ𝕓) ⊥
    | run : ∀ Γ e τ ε,
      typing_reification Γ e (.rep τ) ε →
      closed e →
      typing Γ 𝟙 (.run e) τ ⊥
    | fix₁ : ∀ Γ 𝕊 f τ𝕒 τ𝕓 ε₀ ε₁ ε₂,
      ε₀ = ε₀ ∪ ε₁ →
      typing Γ 𝕊 f (.arrow (.arrow τ𝕒 τ𝕓 ε₀) (.arrow τ𝕒 τ𝕓 ε₀) ε₁) ε₂ →
      typing Γ 𝕊 (.fix₁ f) (.arrow τ𝕒 τ𝕓 ε₀) ε₂
    | fix₂ : ∀ Γ f τ𝕒 τ𝕓 ε,
      typing Γ 𝟙 f (.fragment (.arrow (.arrow τ𝕒 τ𝕓 ⊥) (.arrow τ𝕒 τ𝕓 ⊥) ⊥)) ε →
      typing Γ 𝟙 (.fix₂ f) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | ifz₁ : ∀ Γ 𝕊 c l r τ ε₀ ε₁ ε₂,
      typing Γ 𝕊 c .nat ε₀ →
      typing Γ 𝕊 l τ ε₁ →
      typing Γ 𝕊 r τ ε₂ →
      typing Γ 𝕊 (.ifz₁ c l r) τ (ε₀ ∪ ε₁ ∪ ε₂)
    | ifz₂ : ∀ Γ c l r τ ε₀ ε₁ ε₂,
      typing Γ 𝟙 c (.fragment .nat) ε₀ →
      typing_reification Γ l (.rep τ) ε₁ →
      typing_reification Γ r (.rep τ) ε₂ →
      typing Γ 𝟙 (.ifz₂ c l r) (.fragment τ) ⊤

  inductive typing_reification : TEnv → Expr → Ty → Effect → Prop
    | pure : ∀ Γ e τ, typing Γ 𝟙 e τ ⊥ → typing_reification Γ e τ ⊥
    | reify : ∀ Γ e τ ε, typing Γ 𝟙 e (.fragment τ) ε → typing_reification Γ e (.rep τ) ε
end

lemma typing.regular : ∀ Γ 𝕊 e τ ε, typing Γ 𝕊 e τ ε → lc e :=
  by
  intros Γ 𝕊 e τ ε Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ ε (H : typing Γ 𝕊 e τ ε) => lc e)
      (fun Γ e τ ε (H : typing_reification Γ e τ ε) => lc e)
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

lemma typing_reification.regular : ∀ Γ e τ ε, typing_reification Γ e τ ε → lc e :=
  by
  intros Γ e τ ε Hτ
  cases Hτ <;> (apply typing.regular; assumption)

lemma typing.closed_at_env : ∀ Γ 𝕊 e τ ε, typing Γ 𝕊 e τ ε → closed_at e Γ.length :=
  by
  intros Γ 𝕊 e τ ε Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ ε (H : typing Γ 𝕊 e τ ε) => closed_at e Γ.length)
      (fun Γ e τ ε (H : typing_reification Γ e τ ε) => closed_at e Γ.length)
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

lemma typing_reification.closed_at_env : ∀ Γ e τ ε, typing_reification Γ e τ ε → closed_at e Γ.length :=
  by
  intros Γ e τ ε Hτ
  cases Hτ <;> (apply typing.closed_at_env; assumption)

lemma typing.wf : ∀ Γ 𝕊 e τ ε, typing Γ 𝕊 e τ ε → wf_at e Γ.length :=
  by
  intros Γ 𝕊 e τ ε Hτ
  constructor
  apply typing.regular; apply Hτ
  apply typing.closed_at_env; apply Hτ

lemma typing_reification.wf : ∀ Γ e τ ε, typing_reification Γ e τ ε → wf_at e Γ.length :=
  by
  intros Γ e τ ε Hτ
  cases Hτ <;> (apply typing.wf; assumption)

lemma typing.dynamic_impl_pure : ∀ Γ e τ ε, typing Γ 𝟚 e τ ε → wbt 𝟚 τ ∧ ε = ⊥ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ ε Hτ
  revert HEq𝕊
  apply @typing.rec
    (fun Γ 𝕊 e τ ε (H : typing Γ 𝕊 e τ ε) => 𝟚 = 𝕊 → wbt 𝕊 τ ∧ ε = ⊥)
    (fun Γ e τ ε (H : typing_reification Γ e τ ε) => true)
  <;> intros
  <;> (try assumption)
  <;> (try contradiction)
  case fvar Hwbt HEq𝕊 =>
    constructor; apply Hwbt; rfl
  case lam Hwbt₀ _ IH HEq𝕊 =>
    have ⟨Hwbt₁, Hε₀⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt₀ Hwbt₁
    constructor
    . constructor
      apply Hε₀; constructor
      apply Hwbt₀; apply Hwbt₁
    . rfl
  case app₁ IHf IHarg HEq𝕊 =>
    have ⟨Hwbt₁, Hε₁⟩ := IHf HEq𝕊
    have ⟨Hwbt₂, Hε₂⟩ := IHarg HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt₁ Hwbt₂
    constructor
    . apply Hwbt₁.right.right
    . simp [Hε₁, Hε₂, Hwbt₁.left]
  case lit HEq𝕊 =>
    rw [← HEq𝕊]
    constructor
    . simp
    . rfl
  case binary₁ IHl IHr HEq𝕊 =>
    have ⟨Hwbt₀, Hε₀⟩ := IHl HEq𝕊
    have ⟨Hwbt₁, Hε₁⟩ := IHr HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt₀ Hwbt₁
    constructor
    . simp
    . simp [Hε₀, Hε₁]
  case lets Hwbt Hclose IHb IHe HEq𝕊 =>
    have ⟨Hwbt₀, Hε₀⟩ := IHb HEq𝕊
    have ⟨Hwbt₁, Hε₁⟩ := IHe HEq𝕊
    constructor
    . apply Hwbt₁
    . simp [Hε₀, Hε₁]
  case fix₁ IHf HEq𝕊 =>
    have ⟨Hwbt, Hε⟩ := IHf HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt
    constructor
    . apply Hwbt.right.left
    . simp [Hε]
  case ifz₁ IHc IHl IHr HEq𝕊 =>
    have ⟨Hwbt₀, Hε₀⟩ := IHc HEq𝕊
    have ⟨Hwbt₁, Hε₁⟩ := IHl HEq𝕊
    have ⟨Hwbt₂, Hε₂⟩ := IHr HEq𝕊
    constructor
    . apply Hwbt₂
    . simp [Hε₀, Hε₁, Hε₂]
  case pure => simp
  case reify => simp

lemma typing.dynamic_impl_grounded : ∀ Γ e τ ε, typing Γ 𝟚 e τ ε → grounded e :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ ε Hτ
  revert HEq𝕊
  apply @typing.rec
    (fun Γ 𝕊 e τ ε (H : typing Γ 𝕊 e τ ε) => 𝟚 = 𝕊 → grounded e)
    (fun Γ e τ ε (H : typing_reification Γ e τ ε) => true)
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

lemma typing_reification_code :
  ∀ Γ e τ ε,
    typing_reification Γ (.code e) (.rep τ) ε →
    typing Γ 𝟚 e τ ⊥ :=
  by
  intros Γ e τ ε Hτ
  cases Hτ
  case pure Hτ =>
    cases Hτ
    case code_rep Hτ => apply Hτ
  case reify Hτ =>
    cases Hτ
    case code_fragment Hwbt Hbinds =>
      apply typing.fvar; apply Hbinds; apply Hwbt

lemma typing_diverge : typing ⦰ 𝟚 diverge .nat ⊥ :=
  by
  have Hf : typing ⦰ 𝟚 F (.arrow (.arrow .nat .nat ⊥) (.arrow .nat .nat ⊥) ⊥) ⊥ :=
    by
    rw [F]
    apply typing.lam
    apply typing.lam; rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁
    repeat constructor
  rw [diverge, ← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
  apply typing.app₁
  apply typing.fix₁; simp; rfl; apply Hf
  repeat constructor
