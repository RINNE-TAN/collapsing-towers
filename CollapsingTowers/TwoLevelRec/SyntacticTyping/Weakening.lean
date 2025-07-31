import CollapsingTowers.TwoLevelRec.SyntacticTyping.Typing

theorem typing.weakening.strengthened :
    ∀ Γ Ψ Δ Φ 𝕊 e τ φ,
      typing Γ 𝕊 e τ φ →
      Γ = Ψ ++ Φ →
      typing (Ψ ++ Δ ++ Φ) 𝕊 (shiftl_at Φ.length Δ.length e) τ φ :=
  by
  intros Γ Ψ Δ Φ 𝕊 e τ φ Hτ HEqΓ
  revert Ψ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing (Ψ ++ Δ ++ Φ) 𝕊 (shiftl_at Φ.length Δ.length e) τ φ)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing_reification (Ψ ++ Δ ++ Φ) (shiftl_at Φ.length Δ.length e) τ φ)
  <;> intros
  case fvar x _ Hbinds Hwbt Ψ HEqΓ =>
    rw [HEqΓ] at Hbinds
    by_cases HLe : Φ.length <= x
    . simp only [shiftl_at]; rw [if_pos HLe]; apply typing.fvar
      rw [← Nat.add_sub_of_le HLe]
      rw [← Nat.add_sub_of_le HLe] at Hbinds
      rw [Nat.add_assoc, Nat.add_left_comm, ← Nat.add_assoc, Nat.add_right_comm]
      rw [Nat.add_comm] at Hbinds
      repeat apply binds.extendr
      apply binds.shrinkr; apply Hbinds; apply Hwbt
    . simp only [shiftl_at]; rw [if_neg HLe]; apply typing.fvar
      apply binds.extend; apply binds.shrink
      omega; apply Hbinds; apply Hwbt
  case fix Hwbt Hclose IH Ψ HEqΓ =>
    rw [HEqΓ] at IH Hclose
    have HEq₀ : (Ψ ++ Δ ++ Φ).length = (Ψ ++ Φ).length + Δ.length := by simp; omega
    have HEq₁ : (Ψ ++ Δ ++ Φ).length + 1 = (Ψ ++ Φ).length + 1 + Δ.length := by simp; omega
    rw [comm.shiftl_opening, comm.shiftl_opening] at IH
    apply typing.fix
    rw [← List.cons_append, ← List.cons_append, ← List.cons_append, ← List.cons_append]
    rw [HEq₁, HEq₀]; apply IH; rfl; apply Hwbt
    rw [HEq₀]; apply closed.under_shiftl; apply Hclose
    simp; simp; omega
  case lift_lam IH Ψ HEqΓ =>
    apply typing.lift_lam
    apply IH; apply HEqΓ
  case fix𝕔 Hwbt Hclose IH Ψ HEqΓ =>
    rw [HEqΓ] at IH Hclose
    have HEq₀ : (Ψ ++ Δ ++ Φ).length = (Ψ ++ Φ).length + Δ.length := by simp; omega
    have HEq₁ : (Ψ ++ Δ ++ Φ).length + 1 = (Ψ ++ Φ).length + 1 + Δ.length := by simp; omega
    rw [comm.shiftl_opening, comm.shiftl_opening] at IH
    apply typing.fix𝕔
    rw [← List.cons_append, ← List.cons_append, ← List.cons_append, ← List.cons_append]
    rw [HEq₁, HEq₀]; apply IH; rfl; apply Hwbt
    rw [HEq₀]; apply closed.under_shiftl; apply Hclose
    simp; simp; omega
  case app₁ IHf IHarg Ψ HEqΓ =>
    apply typing.app₁
    apply IHf; apply HEqΓ
    apply IHarg; apply HEqΓ
  case app₂ IHf IHarg Ψ HEqΓ =>
    apply typing.app₂
    apply IHf; apply HEqΓ
    apply IHarg; apply HEqΓ
  case lit => apply typing.lit
  case lift_lit IH Ψ HEqΓ =>
    apply typing.lift_lit
    apply IH; apply HEqΓ
  case code_fragment x _ Hbinds Hwbt Ψ HEqΓ =>
    rw [HEqΓ] at Hbinds
    by_cases HLe : Φ.length <= x
    . simp only [shiftl_at]; rw [if_pos HLe]; apply typing.code_fragment
      rw [← Nat.add_sub_of_le HLe]
      rw [← Nat.add_sub_of_le HLe] at Hbinds
      rw [Nat.add_assoc, Nat.add_left_comm, ← Nat.add_assoc, Nat.add_right_comm]
      rw [Nat.add_comm] at Hbinds
      repeat apply binds.extendr
      apply binds.shrinkr; apply Hbinds; apply Hwbt
    . simp only [shiftl_at]; rw [if_neg HLe]; apply typing.code_fragment
      apply binds.extend; apply binds.shrink
      omega; apply Hbinds; apply Hwbt
  case code_rep IH Ψ HEqΓ =>
    apply typing.code_rep
    apply IH; apply HEqΓ
  case reflect IH Ψ HEqΓ =>
    apply typing.reflect
    apply IH; apply HEqΓ
  case lets Hwbt Hclose IHb IHe Ψ HEqΓ =>
    rw [HEqΓ] at IHe Hclose
    have HEq : (Ψ ++ Δ ++ Φ).length = (Ψ ++ Φ).length + Δ.length := by simp; omega
    rw [comm.shiftl_opening] at IHe
    apply typing.lets
    apply IHb; apply HEqΓ
    rw [← List.cons_append, ← List.cons_append]
    rw [HEq]; apply IHe; rfl; apply Hwbt
    rw [HEq]; apply closed.under_shiftl; apply Hclose
    simp
  case lets𝕔 Hwbt Hclose IHb IHe Ψ HEqΓ =>
    rw [HEqΓ] at IHe Hclose
    have HEq : (Ψ ++ Δ ++ Φ).length = (Ψ ++ Φ).length + Δ.length := by simp; omega
    rw [comm.shiftl_opening] at IHe
    apply typing.lets𝕔
    apply IHb; apply HEqΓ
    rw [← List.cons_append, ← List.cons_append]
    rw [HEq]; apply IHe; rfl; apply Hwbt
    rw [HEq]; apply closed.under_shiftl; apply Hclose
    simp
  case run Hclose IH Ψ HEqΓ =>
    apply typing.run
    apply IH; apply HEqΓ
    rw [identity.shiftl]; apply Hclose
    apply closed.inc; apply Hclose; omega
  case pure IH Ψ HEqΓ =>
    apply typing_reification.pure
    apply IH; apply HEqΓ
  case reify IH Ψ HEqΓ =>
    apply typing_reification.reify
    apply IH; apply HEqΓ
  apply Hτ
