
import CollapsingTowers.TwoLevelPCP.Syntax
import CollapsingTowers.TwoLevelPCP.Shift
import CollapsingTowers.TwoLevelPCP.SmallStep
import CollapsingTowers.TwoLevelPCP.Env
@[simp]
def well_binding_time : Stage → Ty → Prop
  | .stat, .nat => true
  | .stat, (.arrow τ𝕒 τ𝕓 _) => well_binding_time .stat τ𝕒 ∧ well_binding_time .stat τ𝕓
  | .stat, (.fragment τ) => well_binding_time .dyn τ
  | .stat, (.ref τ) => well_binding_time .stat τ
  | .stat, _ => false
  | .dyn, .nat => true
  | .dyn, (.arrow τ𝕒 τ𝕓 φ) => φ = ∅ ∧ well_binding_time .dyn τ𝕒 ∧ well_binding_time .dyn τ𝕓
  | .dyn, (.ref τ) => well_binding_time .dyn τ
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
    | ref _ IH => apply IH; apply HwellBinds

mutual
  inductive typing : TEnv → SEnv → Stage → Expr → Ty → Effects → Prop where
    | fvar : ∀ Γ σ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      well_binding_time 𝕊 τ →
      typing Γ σ 𝕊 (.fvar x) τ ∅
    | lam₁ : ∀ Γ σ 𝕊 e τ𝕒 τ𝕓 φ,
      typing ((τ𝕒, 𝕊) :: Γ) σ 𝕊 (open₀ Γ.length e) τ𝕓 φ →
      well_binding_time 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ σ 𝕊 (.lam₁ e) (.arrow τ𝕒 τ𝕓 φ) ∅
    | lift_lam : ∀ Γ σ e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ σ .stat e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀) φ₁ →
      typing Γ σ .stat (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ∅)) .reify
    | app₁ : ∀ Γ σ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      typing Γ σ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ →
      typing Γ σ 𝕊 arg τ𝕒 φ₂ →
      typing Γ σ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂)
    | app₂ : ∀ Γ σ f arg τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ σ .stat f (.fragment (.arrow τ𝕒 τ𝕓 ∅)) φ₀ →
      typing Γ σ .stat arg (.fragment τ𝕒) φ₁ →
      typing Γ σ .stat (.app₂ f arg) (.fragment τ𝕓) .reify
    | plus₁ : ∀ Γ σ 𝕊 l r φ₀ φ₁,
      typing Γ σ 𝕊 l .nat φ₀ →
      typing Γ σ 𝕊 r .nat φ₁ →
      typing Γ σ 𝕊 (.plus₁ l r) .nat (φ₀ ∪ φ₁)
    | plus₂ : ∀ Γ σ l r φ₀ φ₁,
      typing Γ σ .stat l (.fragment .nat) φ₀ →
      typing Γ σ .stat r (.fragment .nat) φ₁ →
      typing Γ σ .stat (.plus₂ l r) (.fragment .nat) .reify
    | lit₁ : ∀ Γ σ 𝕊 n,
      typing Γ σ 𝕊 (.lit₁ n) .nat ∅
    | lift_lit : ∀ Γ σ n φ,
      typing Γ σ .stat n .nat φ →
      typing Γ σ .stat (.lift n) (.fragment .nat) .reify
    | code_fragment : ∀ Γ σ x τ,
      binds x (τ, .dyn) Γ →
      well_binding_time .dyn τ →
      typing Γ σ .stat (.code (.fvar x)) (.fragment τ) ∅
    | code_rep : ∀ Γ σ e τ,
      typing Γ σ .dyn e τ ∅ →
      typing Γ σ .stat (.code e) (.rep τ) ∅
    | reflect : ∀ Γ σ e τ,
      typing Γ σ .dyn e τ ∅ →
      typing Γ σ .stat (.reflect e) (.fragment τ) .reify
    | lam𝕔 : ∀ Γ σ e τ𝕒 τ𝕓 φ,
      typing_reification ((τ𝕒, .dyn) :: Γ) σ (open₀ Γ.length e) (.rep τ𝕓) φ →
      well_binding_time .dyn τ𝕒 →
      closed_at e Γ.length →
      typing Γ σ .stat (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ∅)) .reify
    | lets : ∀ Γ σ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ σ 𝕊 b τ𝕒 φ₀ →
      typing ((τ𝕒, 𝕊) :: Γ) σ 𝕊 (open₀ Γ.length e) τ𝕓 φ₁ →
      well_binding_time 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ σ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁)
    | let𝕔 : ∀ Γ σ b e τ𝕒 τ𝕓 φ,
      typing Γ σ .dyn b τ𝕒 ∅ →
      typing_reification ((τ𝕒, .dyn) :: Γ) σ (open₀ Γ.length e) (.rep τ𝕓) φ →
      well_binding_time .dyn τ𝕒 →
      closed_at e Γ.length →
      typing Γ σ .stat (.let𝕔 b e) (.rep τ𝕓) ∅
    | run : ∀ Γ σ e τ φ,
      typing_reification Γ σ e (.rep τ) φ →
      closed_at e 0 →
      typing Γ σ .stat (.run e) τ ∅
    | loc : ∀ Γ σ l,
      binds l .nat σ →
      typing Γ σ .stat (.loc l) (.ref .nat) ∅

  inductive typing_reification : TEnv → SEnv → Expr → Ty → Effects → Prop
    | pure : ∀ Γ σ e τ, typing Γ σ .stat e τ ∅ → typing_reification Γ σ e τ ∅
    | reify : ∀ Γ σ e τ φ, typing Γ σ .stat e (.fragment τ) φ → typing_reification Γ σ e (.rep τ) φ
end

@[simp]
def well_store (σ : SEnv) (st : Store) : Prop :=
  σ.length = st.length ∧
  (∀ l e,
    binds l e st →
    binds l .nat σ →
    typing [] σ .stat e .nat ∅
  )

theorem typing_regular : ∀ Γ σ 𝕊 e τ φ, typing Γ σ 𝕊 e τ φ → lc e :=
  by
  intros Γ σ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ σ 𝕊 e τ φ (H : typing Γ σ 𝕊 e τ φ) => lc e)
      (fun Γ σ e τ φ (H : typing_reification Γ σ e τ φ) => lc e)
  <;> (try simp)
  case lam₁ =>
    intros _ _ _ _ _ _ _ _ _ _ IH
    apply open_closedb; apply IH
  case lam𝕔 =>
    intros _ _ _ _ _ _ _ _ _ IH
    apply open_closedb; apply IH
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHf IHarg
    constructor; apply IHf; apply IHarg
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ _ IHf IHarg
    constructor; apply IHf; apply IHarg
  case plus₁ =>
    intros _ _ _ _ _ _ _ _ _ IHl IHr
    constructor; apply IHl; apply IHr
  case plus₂ =>
    intros _ _ _ _ _ _ _ _ IHl IHr
    constructor; apply IHl; apply IHr
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ _ _ IHb IHe
    constructor
    apply IHb; apply open_closedb; apply IHe
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHb IHe
    constructor
    apply IHb; apply open_closedb; apply IHe
  apply Hτ

theorem typing_closed : ∀ Γ σ 𝕊 e τ φ, typing Γ σ 𝕊 e τ φ → closed_at e Γ.length :=
  by
  intros Γ σ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ σ 𝕊 e τ φ (H : typing Γ σ 𝕊 e τ φ) => closed_at e Γ.length)
      (fun Γ σ e τ φ (H : typing_reification Γ σ e τ φ) => closed_at e Γ.length)
  <;> (try intros; assumption)
  case fvar =>
    intros _ _ _ _ _ Hbinds _
    apply indexr_iff_lt.mpr; constructor
    apply Hbinds
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHf IHarg
    constructor; apply IHf; apply IHarg
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ _ IHf IHarg
    constructor; apply IHf; apply IHarg
  case plus₁ =>
    intros _ _ _ _ _ _ _ _ _ IHl IHr
    constructor; apply IHl; apply IHr
  case plus₂ =>
    intros _ _ _ _ _ _ _ _ IHl IHr
    constructor; apply IHl; apply IHr
  case lit₁ => simp
  case code_fragment =>
    intros _ _ _ _ Hbinds _
    apply indexr_iff_lt.mpr; constructor
    apply Hbinds
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ _ Hclose IHb _
    constructor; apply IHb; apply Hclose
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ _ _ Hclose IHb _
    constructor; apply IHb; apply Hclose
  case loc => simp

theorem typing_reification_closed : ∀ Γ σ e τ φ, typing_reification Γ σ e τ φ → closed_at e Γ.length :=
  by
  intros Γ σ e τ φ Hτ
  cases Hτ
  all_goals
    next Hτ =>
      apply typing_closed
      apply Hτ

theorem typing_value_pure : ∀ Γ σ v τ φ, typing Γ σ .stat v τ φ → value v → φ = ∅ :=
  by
  intros _ _ _ _ _ Hτ Hvalue
  cases Hvalue <;> cases Hτ <;> rfl

theorem typing_dyn_pure : ∀ Γ σ e τ φ, typing Γ σ .dyn e τ φ → well_binding_time .dyn τ ∧ φ = ∅ :=
  by
  generalize HEq𝕊 : (.dyn : Stage) = 𝕊
  intros Γ σ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec
    (fun Γ σ 𝕊 e τ φ (H : typing Γ σ 𝕊 e τ φ) => .dyn = 𝕊 → well_binding_time 𝕊 τ ∧ φ = ∅)
    (fun Γ σ e τ φ (H : typing_reification Γ σ e τ φ) => true)
  <;> (try intros; assumption)
  <;> (try intros; contradiction)
  case fvar =>
    intros _ _ _ x _ Hbinds HwellBinds HEq𝕊
    constructor; apply HwellBinds; rfl
  case lam₁ =>
    intros _ _ _ _ _ _ _ _ HwellBinds₀ Hclose IH HEq𝕊
    have ⟨HwellBinds₁, Hφ₀⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at HwellBinds₀ HwellBinds₁
    constructor
    . constructor
      apply Hφ₀; constructor
      apply HwellBinds₀; apply HwellBinds₁
    . rfl
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHf IHarg HEq𝕊
    have ⟨HwellBinds₁, Hφ₁⟩ := IHf HEq𝕊
    have ⟨HwellBinds₂, Hφ₂⟩ := IHarg HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at HwellBinds₁ HwellBinds₂
    constructor
    . apply HwellBinds₁.right.right
    . rw [Hφ₁, Hφ₂, HwellBinds₁.left]; rfl
  case plus₁ =>
    intros _ _ _ _ _ _ _ _ _ IHl IHr HEq𝕊
    have ⟨HwellBinds₁, Hφ₁⟩ := IHl HEq𝕊
    have ⟨HwellBinds₂, Hφ₂⟩ := IHr HEq𝕊
    rw [← HEq𝕊]
    constructor
    . simp
    . rw [Hφ₁, Hφ₂]; rfl
  case lit₁ =>
    intros _ _ _ _ HEq𝕊
    rw [← HEq𝕊]
    constructor
    . simp
    . rfl
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe HEq𝕊
    have ⟨HwellBinds₁, Hφ₁⟩ := IHb HEq𝕊
    have ⟨HwellBinds₂, Hφ₂⟩ := IHe HEq𝕊
    constructor
    . apply HwellBinds₂
    . rw [Hφ₁, Hφ₂]; rfl
  case pure => simp
  case reify => simp

theorem typing_shrink_strengthened :
  ∀ Γ Ψ Δ Φ σ 𝕊 e τ φ,
    typing Γ σ 𝕊 e τ φ →
    Γ = Ψ ++ Φ :: Δ →
    Δ.length ∉ fv e →
    typing (Ψ ++ Δ) σ 𝕊 (shiftr_at Δ.length e) τ φ :=
  by
  intros Γ Ψ Δ Φ σ 𝕊 e τ φ Hτ
  revert Ψ
  apply
    @typing.rec
      (fun Γ σ 𝕊 e τ φ (H : typing Γ σ 𝕊 e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ :: Δ →
          Δ.length ∉ fv e →
          typing (Ψ ++ Δ) σ 𝕊 (shiftr_at Δ.length e) τ φ)
      (fun Γ σ e τ φ (H : typing_reification Γ σ e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ :: Δ →
          Δ.length ∉ fv e →
          typing_reification (Ψ ++ Δ) σ (shiftr_at Δ.length e) τ φ)
  case fvar =>
    intros _ _ _ x _ Hbinds HwellBinds Ψ HEqΓ HcloseΔ
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
  case lam₁ =>
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IH Ψ HEqΓ HcloseΔ
    rw [HEqΓ, shiftr_open₀_comm] at IH
    rw [HEqΓ] at Hclose
    apply typing.lam₁
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
    intros _ _ _ _ _ _ _ _ IH Ψ HEqΓ HcloseΔ
    apply typing.lift_lam
    apply IH; apply HEqΓ; apply HcloseΔ
  case lam𝕔 =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH Ψ HEqΓ HcloseΔ
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
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHf IHarg Ψ HEqΓ HcloseΔ
    simp at HcloseΔ; apply typing.app₁
    apply IHf; apply HEqΓ; apply HcloseΔ.left
    apply IHarg; apply HEqΓ; apply HcloseΔ.right
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ _ IHf IHarg Ψ HEqΓ HcloseΔ
    simp at HcloseΔ; apply typing.app₂
    apply IHf; apply HEqΓ; apply HcloseΔ.left
    apply IHarg; apply HEqΓ; apply HcloseΔ.right
  case plus₁ =>
    intros _ _ _ _ _ _ _ _ _ IHl IHr Ψ HEqΓ HcloseΔ
    simp at HcloseΔ; apply typing.plus₁
    apply IHl; apply HEqΓ; apply HcloseΔ.left
    apply IHr; apply HEqΓ; apply HcloseΔ.right
  case plus₂ =>
    intros _ _ _ _ _ _ _ _ IHl IHr Ψ HEqΓ HcloseΔ
    simp at HcloseΔ; apply typing.plus₂
    apply IHl; apply HEqΓ; apply HcloseΔ.left
    apply IHr; apply HEqΓ; apply HcloseΔ.right
  case lit₁ => intros; apply typing.lit₁
  case lift_lit =>
    intros _ _ _ _ _ IH Ψ HEqΓ HcloseΔ
    apply typing.lift_lit
    apply IH; apply HEqΓ; apply HcloseΔ
  case code_fragment =>
    intros _ _ x _ Hbinds HwellBinds Ψ HEqΓ HcloseΔ
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
    intros _ _ _ _ _ IH Ψ HEqΓ HcloseΔ
    apply typing.code_rep
    apply IH; apply HEqΓ; apply HcloseΔ
  case reflect =>
    intros _ _ _ _ _ IH Ψ HEqΓ HcloseΔ
    apply typing.reflect
    apply IH; apply HEqΓ; apply HcloseΔ
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Ψ HEqΓ HcloseΔ
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
    intros _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Ψ HEqΓ HcloseΔ
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
    intros _ _ _ _ _ _ Hclose IH Ψ HEqΓ HcloseΔ
    apply typing.run
    apply IH; apply HEqΓ; apply HcloseΔ
    rw [shiftr_id]; apply Hclose
    apply closed_inc; apply Hclose; omega
  case loc =>
    intros _ _ _ HbindsLoc Ψ HEqΓ HcloseΔ
    apply typing.loc
    apply HbindsLoc
  case pure =>
    intros _ _ _ _ _ IH Ψ HEqΓ HcloseΔ
    apply typing_reification.pure
    apply IH; apply HEqΓ; apply HcloseΔ
  case reify =>
    intros _ _ _ _ _ _ IH Ψ HEqΓ HcloseΔ
    apply typing_reification.reify
    apply IH; apply HEqΓ; apply HcloseΔ
  apply Hτ

theorem typing_shrink :
  ∀ Γ Φ σ 𝕊 e τ φ,
    typing (Φ :: Γ) σ 𝕊 e τ φ →
    closed_at e Γ.length →
    typing Γ σ 𝕊 e τ φ :=
  by
  intros Γ Φ σ 𝕊 e τ φ Hτ Hclose
  have H := typing_shrink_strengthened (Φ :: Γ) [] Γ Φ σ 𝕊 e τ φ
  rw [shiftr_id] at H
  apply H; apply Hτ; rfl
  apply fv_if_closed_at; apply Hclose; omega
  apply closed_inc; apply Hclose; omega

theorem weakening_strengthened :
    ∀ Γ Ψ Δ Φ σ 𝕊 e τ φ, typing Γ σ 𝕊 e τ φ → Γ = Ψ ++ Φ → typing (Ψ ++ Δ ++ Φ) σ 𝕊 (shiftl_at Φ.length Δ.length e) τ φ :=
  by
  intros Γ Ψ Δ Φ σ 𝕊 e τ φ Hτ HEqΓ
  revert Ψ
  apply
    @typing.rec
      (fun Γ σ 𝕊 e τ φ (H : typing Γ σ 𝕊 e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing (Ψ ++ Δ ++ Φ) σ 𝕊 (shiftl_at (List.length Φ) (List.length Δ) e) τ φ)
      (fun Γ σ e τ φ (H : typing_reification Γ σ e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing_reification (Ψ ++ Δ ++ Φ) σ (shiftl_at (List.length Φ) (List.length Δ) e) τ φ)
  case fvar =>
    intros _ _ _ x _ Hbinds HwellBinds Ψ HEqΓ
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
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IH Ψ HEqΓ
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
    intros _ _ _ _ _ _ _ _ IH Ψ HEqΓ
    apply typing.lift_lam
    apply IH; apply HEqΓ
  case lam𝕔 =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH Ψ HEqΓ
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
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHf IHarg Ψ HEqΓ
    apply typing.app₁
    apply IHf; apply HEqΓ
    apply IHarg; apply HEqΓ
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ _ IHf IHarg Ψ HEqΓ
    apply typing.app₂
    apply IHf; apply HEqΓ
    apply IHarg; apply HEqΓ
  case plus₁ =>
    intros _ _ _ _ _ _ _ _ _ IHl IHr Ψ HEqΓ
    apply typing.plus₁
    apply IHl; apply HEqΓ
    apply IHr; apply HEqΓ
  case plus₂ =>
    intros _ _ _ _ _ _ _ _ IHl IHr Ψ HEqΓ
    apply typing.plus₂
    apply IHl; apply HEqΓ
    apply IHr; apply HEqΓ
  case lit₁ => intros; apply typing.lit₁
  case lift_lit =>
    intros _ _ _ _ _ IH Ψ HEqΓ
    apply typing.lift_lit
    apply IH; apply HEqΓ
  case code_fragment =>
    intros _ _ x _ Hbinds HwellBinds Ψ HEqΓ
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
    intros _ _ _ _ _ IH Ψ HEqΓ
    apply typing.code_rep
    apply IH; apply HEqΓ
  case reflect =>
    intros _ _ _ _ _ IH Ψ HEqΓ
    apply typing.reflect
    apply IH; apply HEqΓ
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Ψ HEqΓ
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
    intros _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Ψ HEqΓ
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
    intros _ _ _ _ _ _ Hclose IH Ψ HEqΓ
    apply typing.run
    apply IH; apply HEqΓ
    rw [shiftl_id]; apply Hclose
    apply closed_inc; apply Hclose; omega
  case loc =>
    intros _ _ _ HbindsLoc Ψ HEqΓ
    apply typing.loc
    apply HbindsLoc
  case pure =>
    intros _ _ _ _ _ IH Ψ HEqΓ
    apply typing_reification.pure
    apply IH; apply HEqΓ
  case reify =>
    intros _ _ _ _ _ _ IH Ψ HEqΓ
    apply typing_reification.reify
    apply IH; apply HEqΓ
  apply Hτ

theorem weakening : ∀ Γ Δ σ 𝕊 e τ φ, typing Γ σ 𝕊 e τ φ → typing (Δ ++ Γ) σ 𝕊 e τ φ :=
  by
  intros Γ Δ σ 𝕊 e τ φ Hτ
  rw [← List.nil_append Δ]
  rw [← shiftl_id _ e]
  apply weakening_strengthened
  apply Hτ; rfl
  apply typing_closed; apply Hτ

theorem weakening1 : ∀ Γ σ 𝕊 e τ𝕒 τ𝕓 φ, typing Γ σ 𝕊 e τ𝕓 φ -> typing (τ𝕒 :: Γ) σ 𝕊 e τ𝕓 φ :=
  by
  intros Γ σ 𝕊 e τ𝕒 τ𝕓 φ
  rw [← List.singleton_append]
  apply weakening

theorem typing_escape_strengthened :
  ∀ Γ σ e τ,
    typing Γ σ .dyn e τ ∅ →
    typing (escape Γ) σ .stat e τ ∅ :=
  by
  generalize HEq𝕊 : (.dyn : Stage) = 𝕊
  intros Γ σ e τ Hτ
  apply
    @typing.rec
      (fun Γ σ 𝕊 e τ φ (H : typing Γ σ 𝕊 e τ φ) =>
          .dyn = 𝕊 →
          typing (escape Γ) σ .stat e τ φ)
      (fun Γ σ e τ φ (H : typing_reification Γ σ e τ φ) => true)
  <;> (try intros; contradiction)
  case fvar =>
    intros _ _ _ x _ Hbinds HwellBinds HEq𝕊
    apply typing.fvar
    apply binds_escape; apply Hbinds
    apply well_binding_time_escape; apply HwellBinds
  case lam₁ =>
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IH HEq𝕊
    rw [← HEq𝕊, escape] at IH
    apply typing.lam₁; rw [← length_escape]
    apply IH; rfl
    apply well_binding_time_escape; apply HwellBinds
    rw [← length_escape]; apply Hclose
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHf IHarg HEq𝕊
    apply typing.app₁
    apply IHf; apply HEq𝕊
    apply IHarg; apply HEq𝕊
  case plus₁ =>
    intros _ _ _ _ _ _ _ _ _ IHl IHr HEq𝕊
    apply typing.plus₁
    apply IHl; apply HEq𝕊
    apply IHr; apply HEq𝕊
  case lit₁ => intros; apply typing.lit₁
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe HEq𝕊
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
  ∀ Γ σ e τ,
    closed_at e 0 →
    typing Γ σ .dyn e τ ∅ →
    typing Γ σ .stat e τ ∅ :=
  by
  intros Γ σ e τ Hclose Hτ
  rw [← List.append_nil Γ]; apply weakening
  rw [nil_escape]; apply typing_escape_strengthened
  induction Γ with
  | nil => apply Hτ
  | cons _ _ IH =>
    apply IH
    apply typing_shrink; apply Hτ
    apply closed_inc; apply Hclose; omega
