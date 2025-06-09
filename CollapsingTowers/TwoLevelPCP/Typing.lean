
import CollapsingTowers.TwoLevelPCP.Syntax
import CollapsingTowers.TwoLevelPCP.Shift
import CollapsingTowers.TwoLevelPCP.SmallStep
import CollapsingTowers.TwoLevelPCP.Env
@[simp]
def well_binding_time : Stage → Ty → Prop
  | .stat, .nat => true
  | .stat, (.arrow τ𝕒 τ𝕓 _) => well_binding_time .stat τ𝕒 ∧ well_binding_time .stat τ𝕓
  | .stat, (.fragment τ) => well_binding_time .dyn τ
  | .stat, _ => false
  | .dyn, .nat => true
  | .dyn, (.arrow τ𝕒 τ𝕓 φ) => φ = ∅ ∧ well_binding_time .dyn τ𝕒 ∧ well_binding_time .dyn τ𝕓
  | .dyn, _ => false

mutual
  inductive typing : TEnv → Stage → Expr → Ty → Effects → Prop where
    | fvar : ∀ Γ 𝕊 x τ,
      binds x τ 𝕊 Γ →
      well_binding_time 𝕊 τ →
      typing Γ 𝕊 (.fvar x) τ ∅
    | lam₁ : ∀ Γ 𝕊 e τ𝕒 τ𝕓 φ,
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 (open₀ Γ.length e) τ𝕓 φ →
      well_binding_time 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lam₁ e) (.arrow τ𝕒 τ𝕓 φ) ∅
    | lift_lam : ∀ Γ e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ .stat e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀) φ₁ →
      typing Γ .stat (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ∅)) .reify
    | app₁ : ∀ Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      typing Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ →
      typing Γ 𝕊 arg τ𝕒 φ₂ →
      typing Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂)
    | app₂ : ∀ Γ f arg τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ .stat f (.fragment (.arrow τ𝕒 τ𝕓 ∅)) φ₀ →
      typing Γ .stat arg (.fragment τ𝕒) φ₁ →
      typing Γ .stat (.app₂ f arg) (.fragment τ𝕓) .reify
    | plus₁ : ∀ Γ 𝕊 l r φ₀ φ₁,
      typing Γ 𝕊 l .nat φ₀ →
      typing Γ 𝕊 r .nat φ₁ →
      typing Γ 𝕊 (.plus₁ l r) .nat (φ₀ ∪ φ₁)
    | plus₂ : ∀ Γ l r φ₀ φ₁,
      typing Γ .stat l (.fragment .nat) φ₀ →
      typing Γ .stat r (.fragment .nat) φ₁ →
      typing Γ .stat (.plus₂ l r) (.fragment .nat) .reify
    | lit₁ : ∀ Γ 𝕊 n,
      typing Γ 𝕊 (.lit₁ n) .nat ∅
    | lift_lit : ∀ Γ n φ,
      typing Γ .stat n .nat φ →
      typing Γ .stat (.lift n) (.fragment .nat) .reify
    | code₁ : ∀ Γ x τ,
      binds x τ .dyn Γ →
      well_binding_time .dyn τ →
      typing Γ .stat (.code (.fvar x)) (.fragment τ) ∅
    | code₂ : ∀ Γ e τ,
      typing Γ .dyn e τ ∅ →
      typing Γ .stat (.code e) (.rep τ) ∅
    | reflect : ∀ Γ e τ,
      typing Γ .dyn e τ ∅ →
      typing Γ .stat (.reflect e) (.fragment τ) .reify
    | lam𝕔 : ∀ Γ e τ𝕒 τ𝕓 φ,
      typing_reification ((τ𝕒, .dyn) :: Γ) (open₀ Γ.length e) (.rep τ𝕓) φ →
      well_binding_time .dyn τ𝕒 →
      closed_at e Γ.length →
      typing Γ .stat (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ∅)) .reify
    | lets : ∀ Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ 𝕊 b τ𝕒 φ₀ →
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 (open₀ Γ.length e) τ𝕓 φ₁ →
      well_binding_time 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁)
    | let𝕔 : ∀ Γ b e τ𝕒 τ𝕓 φ,
      typing Γ .dyn b τ𝕒 ∅ →
      typing_reification ((τ𝕒, .dyn) :: Γ) (open₀ Γ.length e) (.rep τ𝕓) φ →
      well_binding_time .dyn τ𝕒 →
      closed_at e Γ.length →
      typing Γ .stat (.let𝕔 b e) (.rep τ𝕓) ∅

  inductive typing_reification : TEnv → Expr → Ty → Effects → Prop
    | pure : ∀ Γ e τ, typing Γ .stat e τ ∅ → typing_reification Γ e τ ∅
    | reify : ∀ Γ e τ φ, typing Γ .stat e (.fragment τ) φ → typing_reification Γ e (.rep τ) φ
end

theorem typing_regular : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → lc e :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => lc e)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => lc e) <;>
  try simp
  case lam₁ =>
    intros _ _ _ _ _ _ _ _ _ IH
    apply open_closedb; apply IH
  case lam𝕔 =>
    intros _ _ _ _ _ _ _ _ IH
    apply open_closedb; apply IH
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg
    constructor; apply IHf; apply IHarg
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg
    constructor; apply IHf; apply IHarg
  case plus₁ =>
    intros _ _ _ _ _ _ _ _ IHl IHr
    constructor; apply IHl; apply IHr
  case plus₂ =>
    intros _ _ _ _ _ _ _ IHl IHr
    constructor; apply IHl; apply IHr
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHb IHe
    constructor
    apply IHb; apply open_closedb; apply IHe
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ _ _ IHb IHe
    constructor
    apply IHb; apply open_closedb; apply IHe
  apply Hτ

theorem typing_closed : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → closed_at e Γ.length :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => closed_at e Γ.length)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => closed_at e Γ.length) <;>
  try intros; assumption
  case fvar =>
    intros _ _ _ _ Hbinds _
    apply indexrSome'; constructor
    apply Hbinds
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg
    constructor; apply IHf; apply IHarg
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg
    constructor; apply IHf; apply IHarg
  case plus₁ =>
    intros _ _ _ _ _ _ _ _ IHl IHr
    constructor; apply IHl; apply IHr
  case plus₂ =>
    intros _ _ _ _ _ _ _ IHl IHr
    constructor; apply IHl; apply IHr
  case lit₁ => simp
  case code₁ =>
    intros _ _ _ Hbinds _
    apply indexrSome'; constructor
    apply Hbinds
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ Hclose IHb _
    constructor; apply IHb; apply Hclose
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ _ Hclose IHb _
    constructor; apply IHb; apply Hclose

theorem typing_pure : ∀ Γ v τ φ, typing Γ .stat v τ φ → value v → φ = ∅ :=
  by
  intros _ _ _ _ Hτ Hvalue
  cases Hvalue <;> cases Hτ <;> rfl

theorem weakening_strengthened:
    ∀ Γ Ψ Δ Φ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → Γ = Ψ ++ Φ → typing (Ψ ++ Δ ++ Φ) 𝕊 (shiftl_at Φ.length Δ.length e) τ φ :=
  by
  intros Γ Ψ Δ Φ 𝕊 e τ φ Hτ HEqΓ
  revert Ψ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing (Ψ ++ Δ ++ Φ) 𝕊 (shiftl_at (List.length Φ) (List.length Δ) e) τ φ)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing_reification (Ψ ++ Δ ++ Φ) (shiftl_at (List.length Φ) (List.length Δ) e) τ φ)
  case fvar =>
    intros _ _ x _ Hbinds HwellBinds Ψ HEqΓ
    rw [HEqΓ] at Hbinds
    by_cases HLe : Φ.length <= x
    . simp only [shiftl_at]; rw [if_pos HLe]; apply typing.fvar
      rw [← Nat.add_sub_of_le HLe]
      rw [← Nat.add_sub_of_le HLe] at Hbinds
      rw [Nat.add_assoc, Nat.add_left_comm, ← Nat.add_assoc, Nat.add_right_comm]
      rw [Nat.add_comm] at Hbinds
      repeat apply binds_extendr
      apply binds_shrinkr; apply Hbinds; apply HwellBinds
    . simp only [shiftl_at]; rw [if_neg HLe]; apply typing.fvar
      apply binds_extend; apply binds_shrink
      omega; apply Hbinds; apply HwellBinds
  case lam₁ =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH Ψ HEqΓ
    rw [HEqΓ] at IH
    rw [HEqΓ] at Hclose
    rw [shiftl_open₀_comm] at IH
    rw [List.length_append, Nat.add_right_comm] at IH
    apply typing.lam₁
    rw [← List.cons_append, ← List.cons_append, List.length_append, List.length_append]
    apply IH; rfl; apply HwellBinds
    rw [List.length_append, List.length_append, Nat.add_right_comm]
    apply shiftl_closed_at; rw [← List.length_append]; apply Hclose; simp
  case lift_lam =>
    intros _ _ _ _ _ _ _ IH Ψ HEqΓ
    apply typing.lift_lam
    apply IH; apply HEqΓ
  case lam𝕔 =>
    intros _ _ _ _ _ _ HwellBinds Hclose IH Ψ HEqΓ
    rw [HEqΓ] at IH
    rw [HEqΓ] at Hclose
    rw [shiftl_open₀_comm] at IH
    rw [List.length_append, Nat.add_right_comm] at IH
    apply typing.lam𝕔
    rw [← List.cons_append, ← List.cons_append, List.length_append, List.length_append]
    apply IH; rfl; apply HwellBinds
    rw [List.length_append, List.length_append, Nat.add_right_comm]
    apply shiftl_closed_at; rw [← List.length_append]; apply Hclose; simp
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg Ψ HEqΓ
    apply typing.app₁
    apply IHf; apply HEqΓ
    apply IHarg; apply HEqΓ
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg Ψ HEqΓ
    apply typing.app₂
    apply IHf; apply HEqΓ
    apply IHarg; apply HEqΓ
  case plus₁ =>
    intros _ _ _ _ _ _ _ _ IHl IHr Ψ HEqΓ
    apply typing.plus₁
    apply IHl; apply HEqΓ
    apply IHr; apply HEqΓ
  case plus₂ =>
    intros _ _ _ _ _ _ _ IHl IHr Ψ HEqΓ
    apply typing.plus₂
    apply IHl; apply HEqΓ
    apply IHr; apply HEqΓ
  case lit₁ => intros; apply typing.lit₁
  case lift_lit =>
    intros _ _ _ _ IH Ψ HEqΓ
    apply typing.lift_lit
    apply IH; apply HEqΓ
  case code₁ =>
    intros _ x _ Hbinds HwellBinds Ψ HEqΓ
    rw [HEqΓ] at Hbinds
    by_cases HLe : Φ.length <= x
    . simp only [shiftl_at]; rw [if_pos HLe]; apply typing.code₁
      rw [← Nat.add_sub_of_le HLe]
      rw [← Nat.add_sub_of_le HLe] at Hbinds
      rw [Nat.add_assoc, Nat.add_left_comm, ← Nat.add_assoc, Nat.add_right_comm]
      rw [Nat.add_comm] at Hbinds
      repeat apply binds_extendr
      apply binds_shrinkr; apply Hbinds; apply HwellBinds
    . simp only [shiftl_at]; rw [if_neg HLe]; apply typing.code₁
      apply binds_extend; apply binds_shrink
      omega; apply Hbinds; apply HwellBinds
  case code₂ =>
    intros _ _ _ _ IH Ψ HEqΓ
    apply typing.code₂
    apply IH; apply HEqΓ
  case reflect =>
    intros _ _ _ _ IH Ψ HEqΓ
    apply typing.reflect
    apply IH; apply HEqΓ
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Ψ HEqΓ
    rw [HEqΓ] at IHe
    rw [HEqΓ] at Hclose
    rw [shiftl_open₀_comm] at IHe
    rw [List.length_append, Nat.add_right_comm] at IHe
    apply typing.lets
    apply IHb; apply HEqΓ
    rw [← List.cons_append, ← List.cons_append, List.length_append, List.length_append]
    apply IHe; rfl; apply HwellBinds
    rw [List.length_append, List.length_append, Nat.add_right_comm]
    apply shiftl_closed_at; rw [← List.length_append]; apply Hclose; simp
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Ψ HEqΓ
    rw [HEqΓ] at IHe
    rw [HEqΓ] at Hclose
    rw [shiftl_open₀_comm] at IHe
    rw [List.length_append, Nat.add_right_comm] at IHe
    apply typing.let𝕔
    apply IHb; apply HEqΓ
    rw [← List.cons_append, ← List.cons_append, List.length_append, List.length_append]
    apply IHe; rfl; apply HwellBinds
    rw [List.length_append, List.length_append, Nat.add_right_comm]
    apply shiftl_closed_at; rw [← List.length_append]; apply Hclose; simp
  case pure =>
    intros _ _ _ _ IH Ψ HEqΓ
    apply typing_reification.pure
    apply IH; apply HEqΓ
  case reify =>
    intros _ _ _ _ _ IH Ψ HEqΓ
    apply typing_reification.reify
    apply IH; apply HEqΓ
  apply Hτ

theorem weakening : ∀ Γ Δ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → typing (Δ ++ Γ) 𝕊 e τ φ :=
  by
  intros Γ Δ 𝕊 e τ φ Hτ
  rw [← List.nil_append Δ]
  rw [← shiftl_id _ e]
  apply weakening_strengthened
  apply Hτ; rfl
  apply typing_closed; apply Hτ
