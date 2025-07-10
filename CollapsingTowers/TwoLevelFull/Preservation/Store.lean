
import CollapsingTowers.TwoLevelFull.Preservation.Ctx
theorem decompose𝕄_alloc :
  ∀ Γ σ₀ M v τ φ,
    ctx𝕄 Γ.length M →
    value v →
    typing Γ σ₀ .stat (M (.alloc₁ v)) τ φ →
    typing [] σ₀ .stat v .nat ∅ ∧
    ∀ σ₁ loc,
      typing [] (σ₁ ++ σ₀) .stat loc (.ref .nat) ∅ →
      typing Γ (σ₁ ++ σ₀) .stat (M loc) τ φ :=
  by
  intros Γ σ₀ M v τ φ HM Hvalue Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HM
  induction HM generalizing Γ τ φ with
  | hole =>
    cases Hτ
    case alloc₁ Hτv =>
      constructor
      . cases Hvalue <;> try contradiction
        apply typing.lit
      . have Hpure : φ = ∅ := by
          apply typing_value_pure
          apply Hτv; apply Hvalue
        rw [Hpure, ← List.append_nil Γ]
        intro _ _; apply weakening
  | cons𝔹 _ _ HB _ IH =>
    cases HB
    case appl₁ =>
      cases Hτ
      case app₁ Harg HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.app₁
        apply IH; apply Hloc
        apply weakening_store; apply Harg
    case appr₁ =>
      cases Hτ
      case app₁ HX Hf =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.app₁
        apply weakening_store; apply Hf
        apply IH; apply Hloc
    case appl₂ =>
      cases Hτ
      case app₂ HX Harg =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.app₂
        apply IH; apply Hloc
        apply weakening_store; apply Harg
    case appr₂ =>
      cases Hτ
      case app₂ Hf HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.app₂
        apply weakening_store; apply Hf
        apply IH; apply Hloc
    case binaryl₁ =>
      cases Hτ
      case binary₁ HX Hr =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.binary₁
        apply IH; apply Hloc
        apply weakening_store; apply Hr
    case binaryr₁ =>
      cases Hτ
      case binary₁ Hl HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.binary₁
        apply weakening_store; apply Hl
        apply IH; apply Hloc
    case binaryl₂ =>
      cases Hτ
      case binary₂ HX Hr =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.binary₂
        apply IH; apply Hloc
        apply weakening_store; apply Hr
    case binaryr₂ =>
      cases Hτ
      case binary₂ Hl HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.binary₂
        apply weakening_store; apply Hl
        apply IH; apply Hloc
    case lift =>
      cases Hτ
      case lift_lit HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.lift_lit
        apply IH; apply Hloc
      case lift_unit HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.lift_unit
        apply IH; apply Hloc
      case lift_lam HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.lift_lam
        apply IH; apply Hloc
    case lets =>
      cases Hτ
      case lets HwellBinds HX Hclose He =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.lets
        apply IH; apply Hloc
        apply weakening_store; apply He
        apply HwellBinds; apply Hclose
    case load₁ =>
      cases Hτ
      case load₁ HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.load₁
        apply IH; apply Hloc
    case alloc₁ =>
      cases Hτ
      case alloc₁ HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.alloc₁
        apply IH; apply Hloc
    case storel₁ =>
      cases Hτ
      case store₁ HX Hr =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.store₁
        apply IH; apply Hloc
        apply weakening_store; apply Hr
    case storer₁ =>
      cases Hτ
      case store₁ Hl HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.store₁
        apply weakening_store; apply Hl
        apply IH; apply Hloc
    case load₂ =>
      cases Hτ
      case load₂ HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.load₂
        apply IH; apply Hloc
    case alloc₂ =>
      cases Hτ
      case alloc₂ HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.alloc₂
        apply IH; apply Hloc
    case storel₂ =>
      cases Hτ
      case store₂ HX Hr =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.store₂
        apply IH; apply Hloc
        apply weakening_store; apply Hr
    case storer₂ =>
      cases Hτ
      case store₂ Hl HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.store₂
        apply weakening_store; apply Hl
        apply IH; apply Hloc
    case ifz₁ =>
      cases Hτ
      case ifz₁ HX Hl Hr =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.ifz₁
        apply IH; apply Hloc
        apply weakening_store; apply Hl
        apply weakening_store; apply Hr
    case ifz₂ =>
      cases Hτ
      case ifz₂ HX Hl Hr =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.ifz₂
        apply IH; apply Hloc
        apply weakening_store_reification; apply Hl
        apply weakening_store_reification; apply Hr
    case fix₁ =>
      cases Hτ
      case fix₁ HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.fix₁
        apply IH; apply Hloc
    case fix₂ =>
      cases Hτ
      case fix₂ HX =>
        have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
        constructor; apply Hτv
        intros σ₁ loc Hloc
        apply typing.fix₂
        apply IH; apply Hloc
  | consℝ _ _ HR HM IH =>
    cases HR
    case lam𝕔 =>
      cases Hτ
      case lam𝕔 HwellBinds Hclose Hτ =>
        cases Hτ
        case pure HX =>
          rw [← HEqlvl] at HX IH Hclose
          rw [← HEqlvl]
          apply (close_closed _ _ _).mpr at Hclose
          rw [open_close_id₀] at HX
          have ⟨Hτv, IH⟩ := IH _ _ _ HX rfl
          constructor; apply Hτv
          intros σ₁ loc Hloc
          apply typing.lam𝕔; apply typing_reification.pure
          rw [open_close_id₀]; apply IH; apply Hloc
          apply lc_ctx𝕄; apply HM; apply typing_regular; apply Hloc
          apply HwellBinds
          apply (close_closed _ _ _).mp
          apply fv_subset_closed; apply fv_at𝕄 _ _ (.alloc₁ v) loc; apply HM
          rw [(fv_empty_iff_closed loc).mpr]; simp; simp
          rw [← List.length_nil]; apply typing_closed; apply Hloc; apply Hclose
          apply lc_ctx𝕄; apply HM
          simp; apply value_lc; apply Hvalue
        case reify HX =>
          rw [← HEqlvl] at HX IH Hclose
          rw [← HEqlvl]
          apply (close_closed _ _ _).mpr at Hclose
          rw [open_close_id₀] at HX
          have ⟨Hτv, IH⟩ := IH _ _ _ HX rfl
          constructor; apply Hτv
          intros σ₁ loc Hloc
          apply typing.lam𝕔; apply typing_reification.reify
          rw [open_close_id₀]; apply IH; apply Hloc
          apply lc_ctx𝕄; apply HM; apply typing_regular; apply Hloc
          apply HwellBinds
          apply (close_closed _ _ _).mp
          apply fv_subset_closed; apply fv_at𝕄 _ _ (.alloc₁ v) loc; apply HM
          rw [(fv_empty_iff_closed loc).mpr]; simp; simp
          rw [← List.length_nil]; apply typing_closed; apply Hloc; apply Hclose
          apply lc_ctx𝕄; apply HM
          simp; apply value_lc; apply Hvalue
    case let𝕔 =>
      cases Hτ
      case let𝕔 HwellBinds Hτb Hclose Hτ =>
        cases Hτ
        case pure HX =>
          rw [← HEqlvl] at HX IH Hclose
          rw [← HEqlvl]
          apply (close_closed _ _ _).mpr at Hclose
          rw [open_close_id₀] at HX
          have ⟨Hτv, IH⟩ := IH _ _ _ HX rfl
          constructor; apply Hτv
          intros σ₁ loc Hloc
          apply typing.let𝕔; apply weakening_store; apply Hτb
          apply typing_reification.pure
          rw [open_close_id₀]; apply IH; apply Hloc
          apply lc_ctx𝕄; apply HM; apply typing_regular; apply Hloc
          apply HwellBinds
          apply (close_closed _ _ _).mp
          apply fv_subset_closed; apply fv_at𝕄 _ _ (.alloc₁ v) loc; apply HM
          rw [(fv_empty_iff_closed loc).mpr]; simp; simp
          rw [← List.length_nil]; apply typing_closed; apply Hloc; apply Hclose
          apply lc_ctx𝕄; apply HM
          simp; apply value_lc; apply Hvalue
        case reify HX =>
          rw [← HEqlvl] at HX IH Hclose
          rw [← HEqlvl]
          apply (close_closed _ _ _).mpr at Hclose
          rw [open_close_id₀] at HX
          have ⟨Hτv, IH⟩ := IH _ _ _ HX rfl
          constructor; apply Hτv
          intros σ₁ loc Hloc
          apply typing.let𝕔; apply weakening_store; apply Hτb
          apply typing_reification.reify
          rw [open_close_id₀]; apply IH; apply Hloc
          apply lc_ctx𝕄; apply HM; apply typing_regular; apply Hloc
          apply HwellBinds
          apply (close_closed _ _ _).mp
          apply fv_subset_closed; apply fv_at𝕄 _ _ (.alloc₁ v) loc; apply HM
          rw [(fv_empty_iff_closed loc).mpr]; simp; simp
          rw [← List.length_nil]; apply typing_closed; apply Hloc; apply Hclose
          apply lc_ctx𝕄; apply HM
          simp; apply value_lc; apply Hvalue
    case run =>
      cases Hτ
      case run Hclose Hτ =>
        cases Hτ
        case pure HX =>
          have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
          constructor; apply Hτv
          intros σ₁ loc Hloc
          apply typing.run; apply typing_reification.pure
          apply IH; apply Hloc
          apply fv_subset_closed; apply fv_at𝕄 _ _ (.alloc₁ v) loc; apply HM
          rw [(fv_empty_iff_closed loc).mpr]; simp; simp
          rw [← List.length_nil]; apply typing_closed; apply Hloc; apply Hclose
        case reify HX =>
          have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
          constructor; apply Hτv
          intros σ₁ loc Hloc
          apply typing.run; apply typing_reification.reify
          apply IH; apply Hloc
          apply fv_subset_closed; apply fv_at𝕄 _ _ (.alloc₁ v) loc; apply HM
          rw [(fv_empty_iff_closed loc).mpr]; simp; simp
          rw [← List.length_nil]; apply typing_closed; apply Hloc; apply Hclose
    case ifzl₂ =>
      cases Hτ
      case ifz₂ Hτc HX Hτr =>
        cases HX
        case pure HX =>
          have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
          constructor; apply Hτv
          intros σ₁ loc Hloc
          apply typing.ifz₂
          apply weakening_store; apply Hτc
          apply typing_reification.pure; apply IH; apply Hloc
          apply weakening_store_reification; apply Hτr
        case reify HX =>
          have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
          constructor; apply Hτv
          intros σ₁ loc Hloc
          apply typing.ifz₂
          apply weakening_store; apply Hτc
          apply typing_reification.reify; apply IH; apply Hloc
          apply weakening_store_reification; apply Hτr
    case ifzr₂ =>
      cases Hτ
      case ifz₂ Hτc Hτl HX =>
        cases HX
        case pure HX =>
          have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
          constructor; apply Hτv
          intros σ₁ loc Hloc
          apply typing.ifz₂
          apply weakening_store; apply Hτc
          apply weakening_store_reification; apply Hτl
          apply typing_reification.pure; apply IH; apply Hloc
        case reify HX =>
          have ⟨Hτv, IH⟩ := IH _ _ _ HX HEqlvl
          constructor; apply Hτv
          intros σ₁ loc Hloc
          apply typing.ifz₂
          apply weakening_store; apply Hτc
          apply weakening_store_reification; apply Hτl
          apply typing_reification.reify; apply IH; apply Hloc

theorem decompose𝕄_store :
  ∀ Γ σ M e τ φ,
    ctx𝕄 Γ.length M →
    lc e →
    typing Γ σ .stat (M e) τ φ →
    ∃ Γ𝕖 τ𝕖 φ𝕖,
      typing Γ𝕖 σ .stat e τ𝕖 φ𝕖 :=
  by
  intros Γ σ M e τ φ HM Hlc Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HM
  induction HM generalizing Γ τ φ with
  | hole => exists Γ, τ, φ
  | cons𝔹 _ _ HB _ IH =>
    cases HB <;> cases Hτ
    all_goals
      apply IH; assumption; apply HEqlvl
  | consℝ _ _ HR HM IH =>
    cases HR
    case lam𝕔 =>
      cases Hτ
      case lam𝕔 Hτ =>
        cases Hτ
        all_goals
          next Hτ =>
            rw [HEqlvl, open_close_id₀] at Hτ
            apply IH; apply Hτ; simp; omega
            apply lc_ctx𝕄; apply HM; apply Hlc
    case let𝕔 =>
      cases Hτ
      case let𝕔 Hτ =>
        cases Hτ
        all_goals
          next Hτ =>
            rw [HEqlvl, open_close_id₀] at Hτ
            apply IH; apply Hτ; simp; omega
            apply lc_ctx𝕄; apply HM; apply Hlc
    case run =>
      cases Hτ
      case run Hτ =>
        cases Hτ
        all_goals
          apply IH; assumption; apply HEqlvl
    case ifzl₂ =>
      cases Hτ
      case ifz₂ Hτ _ =>
        cases Hτ
        all_goals
          apply IH; assumption; apply HEqlvl
    case ifzr₂ =>
      cases Hτ
      case ifz₂ Hτ =>
        cases Hτ
        all_goals
          apply IH; assumption; apply HEqlvl

theorem preservation_store𝕄 :
  ∀ Γ σ₀ M st₀ st₁ e₀ e₁ τ φ,
    ctx𝕄 Γ.length M →
    lc e₀ →
    shead𝕄 (st₀, e₀) (st₁, e₁) →
    typing Γ σ₀ .stat (M e₀) τ φ →
    well_store σ₀ st₀ →
    ∃ σ₁,
      well_store (σ₁ ++ σ₀) st₁ ∧
      typing Γ (σ₁ ++ σ₀) .stat (M e₁) τ φ :=
    by
    intros Γ σ₀ M st₀ st₁ e₀ e₁ τ φ HM Hlc Hstore𝕄 Hτ HwellStore
    cases Hstore𝕄
    case load₁ l HbindsLoc =>
      have ⟨_, HbindsLocTy⟩ : ∃ τ, binds l τ σ₀ :=
        by
        apply (getr_iff_lt _ _).mp; rw [HwellStore.left]
        apply (getr_iff_lt _ _).mpr; constructor
        apply HbindsLoc
      exists []; constructor
      . apply HwellStore
      . apply decompose𝕄; apply HM; apply Hlc
        . simp; simp [fv_empty_iff_closed]; rw [← List.length_nil]
          apply typing_closed; apply HwellStore.right
          apply HbindsLoc; apply HbindsLocTy
        . intros Γ _ _ Hτ
          cases Hτ with
          | load₁ _ _ _ _ _ Hτ =>
            cases Hτ with
            | loc _ _ _ HbindsLocTy =>
              rw [← List.append_nil Γ]
              apply weakening; apply HwellStore.right
              apply HbindsLoc; apply HbindsLocTy
        . apply Hτ
    case alloc₁ Hvalue =>
      rw [← HwellStore.left]
      have ⟨Hτv, IH⟩ := decompose𝕄_alloc _ _ _ _ _ _ HM Hvalue Hτ
      exists [.nat]; constructor
      . apply well_store_alloc; apply HwellStore; apply Hτv
      . apply IH; apply typing.loc; simp
    case store₁ Hvalue Hpatch =>
      exists []; constructor
      . have ⟨_, _, _, Hτ⟩ := decompose𝕄_store _ _ _ _ _ _ HM Hlc Hτ
        cases Hτ
        case store₁ Hτloc Hτv =>
          cases Hτloc
          case loc HbindsLoc =>
            apply well_store_store; apply HwellStore
            apply Hpatch; apply HbindsLoc
            cases Hvalue <;> try contradiction
            apply typing.lit
      . apply decompose𝕄; apply HM; apply Hlc
        . simp
        . intros Γ _ _ Hτ
          cases Hτ with
          | store₁ _ _ _ _ _ _ _ Hl Hr =>
            cases Hl; apply typing_value_pure at Hr
            rw [Hr Hvalue]; apply typing.unit
        . apply Hτ
