import CollapsingTowers.TwoLvLBasic.SyntacticTyping.Typing

lemma typing.weakening_strengthened :
    ∀ Γ Ψ Δ Φ 𝕊 e τ φ,
      typing Γ 𝕊 e τ φ →
      Γ = Ψ ++ Φ →
      typing (Ψ ++ Δ ++ Φ) 𝕊 ({Φ.length << Δ.length} e) τ φ :=
  by
  intros Γ Ψ Δ Φ 𝕊 e τ φ Hτ HEqΓ
  revert Ψ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing (Ψ ++ Δ ++ Φ) 𝕊 ({Φ.length << Δ.length} e) τ φ)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing_reification (Ψ ++ Δ ++ Φ) ({Φ.length << Δ.length} e) τ φ)
  <;> intros
  case fvar x _ Hbinds HwellBinds Ψ HEqΓ =>
    rw [HEqΓ] at Hbinds
    by_cases HLe : Φ.length <= x
    . simp only [shiftl_at]; rw [if_pos HLe]; apply typing.fvar
      rw [← Nat.add_sub_of_le HLe]
      rw [← Nat.add_sub_of_le HLe] at Hbinds
      rw [Nat.add_assoc, Nat.add_left_comm, ← Nat.add_assoc, Nat.add_right_comm]
      rw [Nat.add_comm] at Hbinds
      repeat apply binds.extendr
      apply binds.shrinkr; apply Hbinds; apply HwellBinds
    . simp only [shiftl_at]; rw [if_neg HLe]; apply typing.fvar
      apply binds.extend; apply binds.shrink
      omega; apply Hbinds; apply HwellBinds
  case lam HwellBinds Hclose IH Ψ HEqΓ =>
    rw [HEqΓ] at IH
    rw [HEqΓ] at Hclose
    rw [comm.shiftl_opening] at IH
    rw [List.length_append, Nat.add_right_comm] at IH
    apply typing.lam
    rw [← List.cons_append, ← List.cons_append, List.length_append, List.length_append]
    apply IH; rfl; apply HwellBinds
    rw [List.length_append, List.length_append, Nat.add_right_comm]
    apply closed.under_shiftl; rw [← List.length_append]; apply Hclose; simp
  case lift_lam IH Ψ HEqΓ =>
    apply typing.lift_lam
    apply IH; apply HEqΓ
  case lam𝕔 HwellBinds Hclose IH Ψ HEqΓ =>
    rw [HEqΓ] at IH
    rw [HEqΓ] at Hclose
    rw [comm.shiftl_opening] at IH
    rw [List.length_append, Nat.add_right_comm] at IH
    apply typing.lam𝕔
    rw [← List.cons_append, ← List.cons_append, List.length_append, List.length_append]
    apply IH; rfl; apply HwellBinds
    rw [List.length_append, List.length_append, Nat.add_right_comm]
    apply closed.under_shiftl; rw [← List.length_append]; apply Hclose; simp
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
  case code_fragment x _ Hbinds HwellBinds Ψ HEqΓ =>
    rw [HEqΓ] at Hbinds
    by_cases HLe : Φ.length <= x
    . simp only [shiftl_at]; rw [if_pos HLe]; apply typing.code_fragment
      rw [← Nat.add_sub_of_le HLe]
      rw [← Nat.add_sub_of_le HLe] at Hbinds
      rw [Nat.add_assoc, Nat.add_left_comm, ← Nat.add_assoc, Nat.add_right_comm]
      rw [Nat.add_comm] at Hbinds
      repeat apply binds.extendr
      apply binds.shrinkr; apply Hbinds; apply HwellBinds
    . simp only [shiftl_at]; rw [if_neg HLe]; apply typing.code_fragment
      apply binds.extend; apply binds.shrink
      omega; apply Hbinds; apply HwellBinds
  case code_rep IH Ψ HEqΓ =>
    apply typing.code_rep
    apply IH; apply HEqΓ
  case reflect IH Ψ HEqΓ =>
    apply typing.reflect
    apply IH; apply HEqΓ
  case lets HwellBinds Hclose IHb IHe Ψ HEqΓ =>
    rw [HEqΓ] at IHe
    rw [HEqΓ] at Hclose
    rw [comm.shiftl_opening] at IHe
    rw [List.length_append, Nat.add_right_comm] at IHe
    apply typing.lets
    apply IHb; apply HEqΓ
    rw [← List.cons_append, ← List.cons_append, List.length_append, List.length_append]
    apply IHe; rfl; apply HwellBinds
    rw [List.length_append, List.length_append, Nat.add_right_comm]
    apply closed.under_shiftl; rw [← List.length_append]; apply Hclose; simp
  case lets𝕔 HwellBinds Hclose IHb IHe Ψ HEqΓ =>
    rw [HEqΓ] at IHe
    rw [HEqΓ] at Hclose
    rw [comm.shiftl_opening] at IHe
    rw [List.length_append, Nat.add_right_comm] at IHe
    apply typing.lets𝕔
    apply IHb; apply HEqΓ
    rw [← List.cons_append, ← List.cons_append, List.length_append, List.length_append]
    apply IHe; rfl; apply HwellBinds
    rw [List.length_append, List.length_append, Nat.add_right_comm]
    apply closed.under_shiftl; rw [← List.length_append]; apply Hclose; simp
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

theorem typing.weakening : ∀ Γ Δ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → typing (Δ ++ Γ) 𝕊 e τ φ :=
  by
  intros Γ Δ 𝕊 e τ φ Hτ
  rw [← List.nil_append Δ]
  rw [← identity.shiftl _ e]
  apply typing.weakening_strengthened
  apply Hτ; rfl
  apply typing.closed_at_env; apply Hτ

theorem typing.weakening_singleton : ∀ Γ 𝕊𝕒 𝕊𝕓 e τ𝕒 τ𝕓 φ, typing Γ 𝕊𝕓 e τ𝕓 φ -> typing ((τ𝕒, 𝕊𝕒) :: Γ) 𝕊𝕓 e τ𝕓 φ :=
  by
  intros Γ 𝕊𝕒 𝕊𝕓 e τ𝕒 τ𝕓 φ
  rw [← List.singleton_append]
  apply typing.weakening
