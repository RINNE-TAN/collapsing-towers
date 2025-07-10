
import CollapsingTowers.TwoLevelBasic.Syntax
import CollapsingTowers.TwoLevelBasic.Shift
import CollapsingTowers.TwoLevelBasic.SmallStep
import CollapsingTowers.TwoLevelBasic.Env
@[simp]
def well_binding_time : Stage → Ty → Prop
  | .stat, .nat => true
  | .stat, (.arrow τ𝕒 τ𝕓 _) => well_binding_time .stat τ𝕒 ∧ well_binding_time .stat τ𝕓
  | .stat, (.fragment τ) => well_binding_time .dyn τ
  | .stat, _ => false
  | .dyn, .nat => true
  | .dyn, (.arrow τ𝕒 τ𝕓 φ) => φ = ∅ ∧ well_binding_time .dyn τ𝕒 ∧ well_binding_time .dyn τ𝕓
  | .dyn, _ => false

theorem well_binding_time_escape : ∀ 𝕊 τ, well_binding_time 𝕊 τ → well_binding_time .stat τ :=
  by
  intros 𝕊 τ HwellBinds
  cases 𝕊
  case stat => assumption
  case dyn =>
    induction τ with
    | nat => simp
    | arrow _ _ _ IH₀ IH₁ =>
      constructor
      apply IH₀; apply HwellBinds.right.left
      apply IH₁; apply HwellBinds.right.right
    | fragment => nomatch HwellBinds
    | rep => nomatch HwellBinds

mutual
  inductive typing : TEnv → Stage → Expr → Ty → Effects → Prop where
    | fvar : ∀ Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      well_binding_time 𝕊 τ →
      typing Γ 𝕊 (.fvar x) τ ∅
    | lam : ∀ Γ 𝕊 e τ𝕒 τ𝕓 φ,
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 (open₀ Γ.length e) τ𝕓 φ →
      well_binding_time 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lam e) (.arrow τ𝕒 τ𝕓 φ) ∅
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
    | lit : ∀ Γ 𝕊 n,
      typing Γ 𝕊 (.lit n) .nat ∅
    | lift_lit : ∀ Γ n φ,
      typing Γ .stat n .nat φ →
      typing Γ .stat (.lift n) (.fragment .nat) .reify
    | code_fragment : ∀ Γ x τ,
      binds x (τ, .dyn) Γ →
      well_binding_time .dyn τ →
      typing Γ .stat (.code (.fvar x)) (.fragment τ) ∅
    | code_rep : ∀ Γ e τ,
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
    | run : ∀ Γ e τ φ,
      typing_reification Γ e (.rep τ) φ →
      closed e →
      typing Γ .stat (.run e) τ ∅

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
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => lc e)
  <;> (try simp)
  case lam =>
    intros _ _ _ _ _ _ _ _ _ IH
    apply (open_lc _ _ _).mp; apply IH
  case lam𝕔 =>
    intros _ _ _ _ _ _ _ _ IH
    apply (open_lc _ _ _).mp; apply IH
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg
    constructor; apply IHf; apply IHarg
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg
    constructor; apply IHf; apply IHarg
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHb IHe
    constructor
    apply IHb; apply (open_lc _ _ _).mp; apply IHe
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ _ _ IHb IHe
    constructor
    apply IHb; apply (open_lc _ _ _).mp; apply IHe
  apply Hτ

theorem typing_reification_regular : ∀ Γ e τ φ, typing_reification Γ e τ φ → lc e :=
  by
  intros Γ e τ φ Hτ
  cases Hτ <;> (apply typing_regular; assumption)

theorem typing_closed : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → closed_at e Γ.length :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => closed_at e Γ.length)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => closed_at e Γ.length)
  <;> (try intros; assumption)
  case fvar =>
    intros _ _ _ _ Hbinds _
    apply (getr_iff_lt _ _).mpr; constructor
    apply Hbinds
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg
    constructor; apply IHf; apply IHarg
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg
    constructor; apply IHf; apply IHarg
  case lit => simp
  case code_fragment =>
    intros _ _ _ Hbinds _
    apply (getr_iff_lt _ _).mpr; constructor
    apply Hbinds
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ Hclose IHb _
    constructor; apply IHb; apply Hclose
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ _ Hclose IHb _
    constructor; apply IHb; apply Hclose

theorem typing_reification_closed : ∀ Γ e τ φ, typing_reification Γ e τ φ → closed_at e Γ.length :=
  by
  intros Γ e τ φ Hτ
  cases Hτ
  all_goals
    next Hτ =>
      apply typing_closed
      apply Hτ

theorem typing_value_pure : ∀ Γ v τ φ, typing Γ .stat v τ φ → value v → φ = ∅ :=
  by
  intros _ _ _ _ Hτ Hvalue
  cases Hvalue <;> cases Hτ <;> rfl

theorem typing_dyn_pure : ∀ Γ e τ φ, typing Γ .dyn e τ φ → well_binding_time .dyn τ ∧ φ = ∅ :=
  by
  generalize HEq𝕊 : (.dyn : Stage) = 𝕊
  intros Γ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec
    (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => .dyn = 𝕊 → well_binding_time 𝕊 τ ∧ φ = ∅)
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

theorem typing_shrink_strengthened :
  ∀ Γ Ψ Δ Φ 𝕊 e τ φ,
    typing Γ 𝕊 e τ φ →
    Γ = Ψ ++ Φ :: Δ →
    Δ.length ∉ fv e →
    typing (Ψ ++ Δ) 𝕊 (shiftr_at Δ.length e) τ φ :=
  by
  intros Γ Ψ Δ Φ 𝕊 e τ φ Hτ
  revert Ψ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ :: Δ →
          Δ.length ∉ fv e →
          typing (Ψ ++ Δ) 𝕊 (shiftr_at Δ.length e) τ φ)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ :: Δ →
          Δ.length ∉ fv e →
          typing_reification (Ψ ++ Δ) (shiftr_at Δ.length e) τ φ)
  case fvar =>
    intros _ _ x _ Hbinds HwellBinds Ψ HEqΓ HcloseΔ
    rw [HEqΓ] at Hbinds; simp
    cases Hx : compare Δ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      rw [if_pos Hx]
      apply typing.fvar
      have Hx : Δ.length <= x - 1 := by omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds_extendr
      rw [← Nat.sub_add_eq, Nat.add_comm]
      apply binds_shrinkr _ (Φ :: Δ)
      rw [List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega; apply HwellBinds
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [Hx] at HcloseΔ; nomatch HcloseΔ
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      rw [if_neg (Nat.not_lt_of_gt Hx)]
      apply typing.fvar
      apply binds_extend; apply binds_shrink
      omega; rw [List.append_cons] at Hbinds; apply Hbinds; apply HwellBinds
  case lam =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH Ψ HEqΓ HcloseΔ
    rw [HEqΓ, shiftr_open₀_comm] at IH
    rw [HEqΓ] at Hclose
    apply typing.lam
    simp; rw [← List.cons_append]
    simp at IH; apply IH; rfl
    apply fv_open₀; apply HcloseΔ; omega
    apply HwellBinds
    cases Ψ with
    | nil =>
      apply shiftr_closed_at_id
      apply fv_closed_at_dec
      apply Hclose; apply HcloseΔ
    | cons =>
      simp at *
      apply shiftr_closed_at; omega
      apply Hclose
    simp; omega
  case lift_lam =>
    intros _ _ _ _ _ _ _ IH Ψ HEqΓ HcloseΔ
    apply typing.lift_lam
    apply IH; apply HEqΓ; apply HcloseΔ
  case lam𝕔 =>
    intros _ _ _ _ _ _ HwellBinds Hclose IH Ψ HEqΓ HcloseΔ
    rw [HEqΓ] at IH; rw [HEqΓ] at Hclose
    rw [shiftr_open₀_comm] at IH
    apply typing.lam𝕔
    simp; rw [← List.cons_append]
    simp at IH; apply IH; rfl
    apply fv_open₀; apply HcloseΔ; omega
    apply HwellBinds
    cases Ψ with
    | nil =>
      apply shiftr_closed_at_id
      apply fv_closed_at_dec
      apply Hclose; apply HcloseΔ
    | cons =>
      simp at *
      apply shiftr_closed_at; omega
      apply Hclose
    simp; omega
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg Ψ HEqΓ HcloseΔ
    simp at HcloseΔ; apply typing.app₁
    apply IHf; apply HEqΓ; apply HcloseΔ.left
    apply IHarg; apply HEqΓ; apply HcloseΔ.right
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg Ψ HEqΓ HcloseΔ
    simp at HcloseΔ; apply typing.app₂
    apply IHf; apply HEqΓ; apply HcloseΔ.left
    apply IHarg; apply HEqΓ; apply HcloseΔ.right
  case lit => intros; apply typing.lit
  case lift_lit =>
    intros _ _ _ _ IH Ψ HEqΓ HcloseΔ
    apply typing.lift_lit
    apply IH; apply HEqΓ; apply HcloseΔ
  case code_fragment =>
    intros _ x _ Hbinds HwellBinds Ψ HEqΓ HcloseΔ
    rw [HEqΓ] at Hbinds; simp
    cases Hx : compare Δ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      rw [if_pos Hx]
      apply typing.code_fragment
      have Hx : Δ.length <= x - 1 := by omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds_extendr
      rw [← Nat.sub_add_eq, Nat.add_comm]
      apply binds_shrinkr _ (Φ :: Δ)
      rw [List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega; apply HwellBinds
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [Hx] at HcloseΔ; nomatch HcloseΔ
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      rw [if_neg (Nat.not_lt_of_gt Hx)]
      apply typing.code_fragment
      apply binds_extend; apply binds_shrink
      omega; rw [List.append_cons] at Hbinds; apply Hbinds; apply HwellBinds
  case code_rep =>
    intros _ _ _ _ IH Ψ HEqΓ HcloseΔ
    apply typing.code_rep
    apply IH; apply HEqΓ; apply HcloseΔ
  case reflect =>
    intros _ _ _ _ IH Ψ HEqΓ HcloseΔ
    apply typing.reflect
    apply IH; apply HEqΓ; apply HcloseΔ
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Ψ HEqΓ HcloseΔ
    rw [HEqΓ] at IHb; rw [HEqΓ] at IHe; rw [HEqΓ] at Hclose
    rw [shiftr_open₀_comm] at IHe
    simp at IHb; simp at IHe; simp at HcloseΔ
    apply typing.lets
    apply IHb; apply HcloseΔ.left
    simp; rw [← List.cons_append]; apply IHe; rfl
    apply fv_open₀; apply HcloseΔ.right; omega
    apply HwellBinds
    cases Ψ with
    | nil =>
      apply shiftr_closed_at_id
      apply fv_closed_at_dec
      apply Hclose; apply HcloseΔ.right
    | cons =>
      simp at *
      apply shiftr_closed_at; omega
      apply Hclose
    simp; omega
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Ψ HEqΓ HcloseΔ
    rw [HEqΓ] at IHb; rw [HEqΓ] at IHe; rw [HEqΓ] at Hclose
    rw [shiftr_open₀_comm] at IHe
    simp at IHb; simp at IHe; simp at HcloseΔ
    apply typing.let𝕔
    apply IHb; apply HcloseΔ.left
    simp; rw [← List.cons_append]; apply IHe; rfl
    apply fv_open₀; apply HcloseΔ.right; omega
    apply HwellBinds
    cases Ψ with
    | nil =>
      apply shiftr_closed_at_id
      apply fv_closed_at_dec
      apply Hclose; apply HcloseΔ.right
    | cons =>
      simp at *
      apply shiftr_closed_at; omega
      apply Hclose
    simp; omega
  case run =>
    intros _ _ _ _ _ Hclose IH Ψ HEqΓ HcloseΔ
    apply typing.run
    apply IH; apply HEqΓ; apply HcloseΔ
    rw [shiftr_id]; apply Hclose
    apply closed_inc; apply Hclose; omega
  case pure =>
    intros _ _ _ _ IH Ψ HEqΓ HcloseΔ
    apply typing_reification.pure
    apply IH; apply HEqΓ; apply HcloseΔ
  case reify =>
    intros _ _ _ _ _ IH Ψ HEqΓ HcloseΔ
    apply typing_reification.reify
    apply IH; apply HEqΓ; apply HcloseΔ
  apply Hτ

theorem typing_shrink :
  ∀ Γ Φ 𝕊 e τ φ,
    typing (Φ :: Γ) 𝕊 e τ φ →
    closed_at e Γ.length →
    typing Γ 𝕊 e τ φ :=
  by
  intros Γ Φ 𝕊 e τ φ Hτ Hclose
  have H := typing_shrink_strengthened (Φ :: Γ) [] Γ Φ 𝕊 e τ φ
  rw [shiftr_id] at H
  apply H; apply Hτ; rfl
  apply fv_if_closed_at; apply Hclose; omega
  apply closed_inc; apply Hclose; omega

theorem weakening_strengthened :
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
  case lam =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH Ψ HEqΓ
    rw [HEqΓ] at IH
    rw [HEqΓ] at Hclose
    rw [shiftl_open₀_comm] at IH
    rw [List.length_append, Nat.add_right_comm] at IH
    apply typing.lam
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
  case lit => intros; apply typing.lit
  case lift_lit =>
    intros _ _ _ _ IH Ψ HEqΓ
    apply typing.lift_lit
    apply IH; apply HEqΓ
  case code_fragment =>
    intros _ x _ Hbinds HwellBinds Ψ HEqΓ
    rw [HEqΓ] at Hbinds
    by_cases HLe : Φ.length <= x
    . simp only [shiftl_at]; rw [if_pos HLe]; apply typing.code_fragment
      rw [← Nat.add_sub_of_le HLe]
      rw [← Nat.add_sub_of_le HLe] at Hbinds
      rw [Nat.add_assoc, Nat.add_left_comm, ← Nat.add_assoc, Nat.add_right_comm]
      rw [Nat.add_comm] at Hbinds
      repeat apply binds_extendr
      apply binds_shrinkr; apply Hbinds; apply HwellBinds
    . simp only [shiftl_at]; rw [if_neg HLe]; apply typing.code_fragment
      apply binds_extend; apply binds_shrink
      omega; apply Hbinds; apply HwellBinds
  case code_rep =>
    intros _ _ _ _ IH Ψ HEqΓ
    apply typing.code_rep
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
  case run =>
    intros _ _ _ _ _ Hclose IH Ψ HEqΓ
    apply typing.run
    apply IH; apply HEqΓ
    rw [shiftl_id]; apply Hclose
    apply closed_inc; apply Hclose; omega
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

theorem weakening1 : ∀ Γ 𝕊 e τ𝕒 τ𝕓 φ, typing Γ 𝕊 e τ𝕓 φ -> typing (τ𝕒 :: Γ) 𝕊 e τ𝕓 φ :=
  by
  intros Γ 𝕊 e τ𝕒 τ𝕓 φ
  rw [← List.singleton_append]
  apply weakening

theorem weakening_reification : ∀ Γ Δ e τ φ, typing_reification Γ e τ φ → typing_reification (Δ ++ Γ) e τ φ :=
  by
  intros Γ Δ e τ φ Hτ
  rw [← List.nil_append Δ]
  rw [← shiftl_id _ e]
  cases Hτ
  case pure Hτ =>
    apply typing_reification.pure
    apply weakening_strengthened
    apply Hτ; rfl
  case reify Hτ =>
    apply typing_reification.reify
    apply weakening_strengthened
    apply Hτ; rfl
  apply typing_reification_closed; apply Hτ

theorem typing_escape_strengthened :
  ∀ Γ e τ,
    typing Γ .dyn e τ ∅ →
    typing (escape Γ) .stat e τ ∅ :=
  by
  generalize HEq𝕊 : (.dyn : Stage) = 𝕊
  intros Γ e τ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
          .dyn = 𝕊 →
          typing (escape Γ) .stat e τ φ)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => true)
  <;> (try intros; contradiction)
  case fvar =>
    intros _ _ x _ Hbinds HwellBinds HEq𝕊
    apply typing.fvar
    apply binds_escape; apply Hbinds
    apply well_binding_time_escape; apply HwellBinds
  case lam =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH HEq𝕊
    rw [← HEq𝕊, escape] at IH
    apply typing.lam; rw [← length_escape]
    apply IH; rfl
    apply well_binding_time_escape; apply HwellBinds
    rw [← length_escape]; apply Hclose
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg HEq𝕊
    apply typing.app₁
    apply IHf; apply HEq𝕊
    apply IHarg; apply HEq𝕊
  case lit => intros; apply typing.lit
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe HEq𝕊
    rw [← HEq𝕊, escape] at IHe
    apply typing.lets
    apply IHb; apply HEq𝕊
    rw [← length_escape]; apply IHe; rfl
    apply well_binding_time_escape; apply HwellBinds
    rw [← length_escape]; apply Hclose
  case pure => simp
  case reify => simp
  apply Hτ; apply HEq𝕊

theorem typing_escape :
  ∀ Γ e τ,
    closed e →
    typing Γ .dyn e τ ∅ →
    typing Γ .stat e τ ∅ :=
  by
  intros Γ e τ Hclose Hτ
  rw [← List.append_nil Γ]; apply weakening
  rw [nil_escape]; apply typing_escape_strengthened
  induction Γ with
  | nil => apply Hτ
  | cons _ _ IH =>
    apply IH
    apply typing_shrink; apply Hτ
    apply closed_inc; apply Hclose; omega
