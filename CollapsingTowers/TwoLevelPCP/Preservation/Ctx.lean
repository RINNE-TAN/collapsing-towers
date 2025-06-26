
import Mathlib.Tactic
import CollapsingTowers.TwoLevelPCP.Typing
theorem decomposeℝ_head :
  ∀ intro Γ σ R e₀ e₁ τ φ₀,
    ctxℝ intro Γ.length R →
    lc e₀ →
    (∀ Δ τ φ₀,
      Δ.length = intro →
      typing (Δ ++ Γ) σ .stat e₀ τ φ₀ →
      ∃ φ₁,
        typing (Δ ++ Γ) σ .stat e₁ τ φ₁ ∧
        φ₁ ≤ φ₀
    ) →
    fv e₁ ⊆ fv e₀ →
    typing Γ σ .stat (R e₀) τ φ₀ →
    ∃ φ₁,
      typing Γ σ .stat (R e₁) τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros intro Γ σ R e₀ e₁ τ φ₀ HR Hlc IH Hsubst Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 HwellBinds Hclose IHe =>
      rw [open_close_id₀] at IHe
      . cases IHe with
        | pure _ _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          have ⟨_, IHe₀, Hφ⟩ := IH _ _ _ rfl IHe₀
          rw [le_pure _ Hφ] at IHe₀
          constructor; constructor
          apply typing.lam𝕔
          apply typing_reification.pure
          rw [open_close_id₀]
          apply IHe₀; apply typing_regular; apply IHe₀
          apply HwellBinds
          apply (close_closed _ _ _).mp; rw [← List.length_cons]
          apply typing_closed; apply IHe₀; rfl
        | reify _ _ _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          have ⟨_, IHe₀, Hφ⟩ := IH _ _ _ rfl IHe₀
          constructor; constructor
          apply typing.lam𝕔
          apply typing_reification.reify
          rw [open_close_id₀]
          apply IHe₀; apply typing_regular; apply IHe₀
          apply HwellBinds
          apply (close_closed _ _ _).mp; rw [← List.length_cons]
          apply typing_closed; apply IHe₀; rfl
      apply Hlc
  case let𝕔 =>
    cases Hτ
    case let𝕔 HwellBinds IHb Hclose IHe =>
      rw [open_close_id₀] at IHe
      . cases IHe with
        | pure _ _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          have ⟨_, IHe₀, Hφ⟩ := IH _ _ _ rfl IHe₀
          rw [le_pure _ Hφ] at IHe₀
          constructor; constructor
          apply typing.let𝕔; apply IHb
          apply typing_reification.pure
          rw [open_close_id₀]
          apply IHe₀; apply typing_regular; apply IHe₀
          apply HwellBinds
          apply (close_closed _ _ _).mp; rw [← List.length_cons]
          apply typing_closed; apply IHe₀; rfl
        | reify _ _ _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          have ⟨_, IHe₀, Hφ⟩ := IH _ _ _ rfl IHe₀
          constructor; constructor
          apply typing.let𝕔; apply IHb
          apply typing_reification.reify
          rw [open_close_id₀]
          apply IHe₀; apply typing_regular; apply IHe₀
          apply HwellBinds
          apply (close_closed _ _ _).mp; rw [← List.length_cons]
          apply typing_closed; apply IHe₀; rfl
      apply Hlc
  case run =>
    cases Hτ
    case run Hclose Hτ =>
      cases Hτ with
      | pure _ _ _ _ IHe₀ =>
        rw [← List.nil_append Γ] at IHe₀
        have ⟨_, IHe₀, Hφ⟩ := IH _ _ _ rfl IHe₀
        rw [le_pure _ Hφ] at IHe₀
        constructor; constructor
        apply typing.run
        apply typing_reification.pure
        apply IHe₀
        rw [← fv_empty_iff_closed]
        rw [← fv_empty_iff_closed] at Hclose
        rw [Hclose] at Hsubst
        simp at Hsubst; apply Hsubst; rfl
      | reify _ _ _ _ _ IHe₀ =>
        rw [← List.nil_append Γ] at IHe₀
        have ⟨_, IHe₀, Hφ⟩ := IH _ _ _ rfl IHe₀
        constructor; constructor
        apply typing.run
        apply typing_reification.reify
        apply IHe₀
        rw [← fv_empty_iff_closed]
        rw [← fv_empty_iff_closed] at Hclose
        rw [Hclose] at Hsubst
        simp at Hsubst; apply Hsubst; rfl
  case ifzl₂ =>
    cases Hτ
    case ifz₂ Hτc IHe₀ Hτr =>
      cases IHe₀
      case pure IHe₀ =>
        rw [← List.nil_append Γ] at IHe₀
        have ⟨_, IHe₀, Hφ⟩ := IH _ _ _ rfl IHe₀
        rw [le_pure _ Hφ] at IHe₀
        constructor; constructor
        apply typing.ifz₂
        apply Hτc
        apply typing_reification.pure
        apply IHe₀; apply Hτr; rfl
      case reify IHe₀ =>
        rw [← List.nil_append Γ] at IHe₀
        have ⟨_, IHe₀, Hφ⟩ := IH _ _ _ rfl IHe₀
        constructor; constructor
        apply typing.ifz₂
        apply Hτc
        apply typing_reification.reify
        apply IHe₀; apply Hτr; rfl
  case ifzr₂ =>
    cases Hτ
    case ifz₂ Hτc Hτl IHe₀ =>
      cases IHe₀
      case pure IHe₀ =>
        rw [← List.nil_append Γ] at IHe₀
        have ⟨_, IHe₀, Hφ⟩ := IH _ _ _ rfl IHe₀
        rw [le_pure _ Hφ] at IHe₀
        constructor; constructor
        apply typing.ifz₂
        apply Hτc; apply Hτl
        apply typing_reification.pure
        apply IHe₀; rfl
      case reify IHe₀ =>
        rw [← List.nil_append Γ] at IHe₀
        have ⟨_, IHe₀, Hφ⟩ := IH _ _ _ rfl IHe₀
        constructor; constructor
        apply typing.ifz₂
        apply Hτc; apply Hτl
        apply typing_reification.reify
        apply IHe₀; rfl

theorem decompose𝔹_head :
  ∀ Γ σ B e₀ e₁ τ φ₀,
    ctx𝔹 B →
    (∀ τ φ₀,
      typing Γ σ .stat e₀ τ φ₀ →
      ∃ φ₁,
        typing Γ σ .stat e₁ τ φ₁ ∧
        φ₁ ≤ φ₀
    ) →
    typing Γ σ .stat (B e₀) τ φ₀ →
    ∃ φ₁,
      typing Γ σ .stat (B e₁) τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros Γ σ B e₀ e₁ τ φ₀ HB IH Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ IHarg IHf =>
      have ⟨_, IHf, Hφ⟩ := IH _ _ IHf
      constructor; constructor
      apply typing.app₁
      apply IHf; apply IHarg
      apply le_union_left; apply le_union_right; apply Hφ
  case appr₁ =>
    cases Hτ
    case app₁ IHarg IHf =>
      have ⟨_, IHarg, Hφ⟩ := IH _ _ IHarg
      constructor; constructor
      apply typing.app₁
      apply IHf; apply IHarg
      apply le_union_right; apply Hφ
  case appl₂ =>
    cases Hτ
    case app₂ IHf IHarg =>
      have ⟨_, IHf, Hφ⟩ := IH _ _ IHf
      constructor; constructor
      apply typing.app₂
      apply IHf; apply IHarg
      rfl
  case appr₂ =>
    cases Hτ
    case app₂ IHf IHarg =>
      have ⟨_, IHarg, Hφ⟩ := IH _ _ IHarg
      constructor; constructor
      apply typing.app₂
      apply IHf; apply IHarg
      rfl
  case binaryl₁ =>
    cases Hτ
    case binary₁ IHl IHr =>
      have ⟨_, IHl, Hφ⟩ := IH _ _ IHl
      constructor; constructor
      apply typing.binary₁
      apply IHl; apply IHr
      apply le_union_left; apply Hφ
  case binaryr₁ =>
    cases Hτ
    case binary₁ IHl IHr =>
      have ⟨_, IHr, Hφ⟩ := IH _ _ IHr
      constructor; constructor
      apply typing.binary₁
      apply IHl; apply IHr
      apply le_union_right; apply Hφ
  case binaryl₂ =>
    cases Hτ
    case binary₂ IHl IHr =>
      have ⟨_, IHl, Hφ⟩ := IH _ _ IHl
      constructor; constructor
      apply typing.binary₂
      apply IHl; apply IHr
      rfl
  case binaryr₂ =>
    cases Hτ
    case binary₂ IHl IHr =>
      have ⟨_, IHr, Hφ⟩ := IH _ _ IHr
      constructor; constructor
      apply typing.binary₂
      apply IHl; apply IHr
      rfl
  case lift =>
    cases Hτ
    case lift_lit IHn =>
      have ⟨_, IHn, Hφ⟩ := IH _ _ IHn
      constructor; constructor
      apply typing.lift_lit
      apply IHn
      rfl
    case lift_lam IHe =>
      have ⟨_, IHe, Hφ⟩ := IH _ _ IHe
      constructor; constructor
      apply typing.lift_lam
      apply IHe
      rfl
  case lets =>
    cases Hτ
    case lets HwellBinds IHb Hclose IHe =>
      have ⟨_, IHb, Hφ⟩ := IH _ _ IHb
      constructor; constructor
      apply typing.lets
      apply IHb; apply IHe
      apply HwellBinds; apply Hclose
      apply le_union_left; apply Hφ
  case load₁ =>
    cases Hτ
    case load₁ IHe =>
      have ⟨_, IHe, Hφ⟩ := IH _ _ IHe
      constructor; constructor
      apply typing.load₁
      apply IHe
      apply Hφ
  case alloc₁ =>
    cases Hτ
    case alloc₁ IHe =>
      have ⟨_, IHe, Hφ⟩ := IH _ _ IHe
      constructor; constructor
      apply typing.alloc₁
      apply IHe
      apply Hφ
  case storel₁ =>
    cases Hτ
    case store₁ IHl IHr =>
      have ⟨_, IHl, Hφ⟩ := IH _ _ IHl
      constructor; constructor
      apply typing.store₁
      apply IHl; apply IHr
      apply le_union_left; apply Hφ
  case storer₁ =>
    cases Hτ
    case store₁ IHl IHr =>
      have ⟨_, IHr, Hφ⟩ := IH _ _ IHr
      constructor; constructor
      apply typing.store₁
      apply IHl; apply IHr
      apply le_union_right; apply Hφ
  case load₂ =>
    cases Hτ
    case load₂ IHe =>
      have ⟨_, IHe, Hφ⟩ := IH _ _ IHe
      constructor; constructor
      apply typing.load₂
      apply IHe
      rfl
  case alloc₂ =>
    cases Hτ
    case alloc₂ IHe =>
      have ⟨_, IHe, Hφ⟩ := IH _ _ IHe
      constructor; constructor
      apply typing.alloc₂
      apply IHe
      rfl
  case storel₂ =>
    cases Hτ
    case store₂ IHl IHr =>
      have ⟨_, IHl, Hφ⟩ := IH _ _ IHl
      constructor; constructor
      apply typing.store₂
      apply IHl; apply IHr
      rfl
  case storer₂ =>
    cases Hτ
    case store₂ IHl IHr =>
      have ⟨_, IHr, Hφ⟩ := IH _ _ IHr
      constructor; constructor
      apply typing.store₂
      apply IHl; apply IHr
      rfl
  case ifz₁ =>
    cases Hτ
    case ifz₁ IHc IHl IHr =>
      have ⟨_, IHc, Hφ⟩ := IH _ _ IHc
      constructor; constructor
      apply typing.ifz₁
      apply IHc; apply IHl; apply IHr
      apply le_union_left; apply Hφ
  case ifz₂ =>
    cases Hτ
    case ifz₂ IHc IHl IHr =>
      have ⟨_, IHc, Hφ⟩ := IH _ _ IHc
      constructor; constructor
      apply typing.ifz₂
      apply IHc; apply IHl; apply IHr
      rfl
  case fix₁ =>
    cases Hτ
    case fix₁ IHe =>
      have ⟨_, IHe, Hφ⟩ := IH _ _ IHe
      constructor; constructor
      apply typing.fix₁
      apply IHe
      apply Hφ
  case fix₂ =>
    cases Hτ
    case fix₂ IHe =>
      have ⟨_, IHe, Hφ⟩ := IH _ _ IHe
      constructor; constructor
      apply typing.fix₂
      apply IHe
      rfl

theorem decompose𝕄_head :
  ∀ Γ σ M e₀ e₁ τ φ₀,
    ctx𝕄 Γ.length M →
    lc e₀ →
    fv e₁ ⊆ fv e₀ →
    (∀ Γ τ φ₀,
      typing Γ σ .stat e₀ τ φ₀ →
      ∃ φ₁,
        typing Γ σ .stat e₁ τ φ₁ ∧
        φ₁ ≤ φ₀
    ) →
    typing Γ σ .stat (M e₀) τ φ₀ →
    ∃ φ₁,
      typing Γ σ .stat (M e₁) τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros Γ σ M e₀ e₁ τ φ₀ HM Hlc HFv IH Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HM
  induction HM generalizing τ φ₀ Γ with
  | hole => apply IH; apply Hτ
  | cons𝔹 _ _ HB _ IHM =>
    rw [← ctx_comp]; apply decompose𝔹_head
    apply HB; intros _ _ IHτ
    apply IHM; apply IHτ; apply HEqlvl; apply Hτ
  | consℝ _ _ HR HM IHM =>
    rw [← ctx_comp]; apply decomposeℝ_head
    rw [HEqlvl]; apply HR
    apply lc_ctx𝕄
    apply HM; apply Hlc
    . intros _ _ _ _ IHτ
      apply IHM; apply IHτ; simp; omega
    . apply fv_at𝕄; apply HM
      apply HFv
    apply Hτ

theorem decomposeℝ :
  ∀ intro Γ σ R e₀ e₁ τ φ,
    ctxℝ intro Γ.length R →
    lc e₀ →
    (∀ Δ τ φ,
      Δ.length = intro →
      typing (Δ ++ Γ) σ .stat e₀ τ φ →
      typing (Δ ++ Γ) σ .stat e₁ τ φ
    ) →
    fv e₁ ⊆ fv e₀ →
    typing Γ σ .stat (R e₀) τ φ →
    typing Γ σ .stat (R e₁) τ φ :=
  by
  intros intro Γ σ R e₀ e₁ τ φ HR Hlc IH Hsubst Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 HwellBinds Hclose IHe =>
      rw [open_close_id₀] at IHe
      . cases IHe with
        | pure _ _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          apply IH at IHe₀
          apply typing.lam𝕔
          apply typing_reification.pure
          rw [open_close_id₀]
          apply IHe₀; apply typing_regular; apply IHe₀
          apply HwellBinds
          apply (close_closed _ _ _).mp; rw [← List.length_cons]
          apply typing_closed; apply IHe₀; rfl
        | reify _ _ _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          apply IH at IHe₀
          apply typing.lam𝕔
          apply typing_reification.reify
          rw [open_close_id₀]
          apply IHe₀; apply typing_regular; apply IHe₀
          apply HwellBinds
          apply (close_closed _ _ _).mp; rw [← List.length_cons]
          apply typing_closed; apply IHe₀; rfl
      apply Hlc
  case let𝕔 =>
    cases Hτ
    case let𝕔 HwellBinds IHb Hclose IHe =>
      rw [open_close_id₀] at IHe
      . cases IHe with
        | pure _ _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          apply IH at IHe₀
          apply typing.let𝕔; apply IHb
          apply typing_reification.pure
          rw [open_close_id₀]
          apply IHe₀; apply typing_regular; apply IHe₀
          apply HwellBinds
          apply (close_closed _ _ _).mp; rw [← List.length_cons]
          apply typing_closed; apply IHe₀; rfl
        | reify _ _ _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          apply IH at IHe₀
          apply typing.let𝕔; apply IHb
          apply typing_reification.reify
          rw [open_close_id₀]
          apply IHe₀; apply typing_regular; apply IHe₀
          apply HwellBinds
          apply (close_closed _ _ _).mp; rw [← List.length_cons]
          apply typing_closed; apply IHe₀; rfl
      apply Hlc
  case run =>
    cases Hτ
    case run Hclose Hτ =>
      cases Hτ with
      | pure _ _ _ _ Hτ =>
        apply typing.run
        apply typing_reification.pure
        rw [← List.nil_append Γ]
        apply IH; simp; apply Hτ
        rw [← fv_empty_iff_closed]
        rw [← fv_empty_iff_closed] at Hclose
        rw [Hclose] at Hsubst
        simp at Hsubst; apply Hsubst
      | reify _ _ _ _ _ Hτ =>
        apply typing.run
        apply typing_reification.reify
        rw [← List.nil_append Γ]
        apply IH; simp; apply Hτ
        rw [← fv_empty_iff_closed]
        rw [← fv_empty_iff_closed] at Hclose
        rw [Hclose] at Hsubst
        simp at Hsubst; apply Hsubst
  case ifzl₂ =>
    cases Hτ
    case ifz₂ Hτc Hτl Hτr =>
      cases Hτl
      case pure Hτl =>
        apply typing.ifz₂
        apply Hτc
        apply typing_reification.pure
        rw [← List.nil_append Γ]; apply IH; rfl
        apply Hτl; apply Hτr
      case reify Hτl =>
        apply typing.ifz₂
        apply Hτc
        apply typing_reification.reify
        rw [← List.nil_append Γ]; apply IH; rfl
        apply Hτl; apply Hτr
  case ifzr₂ =>
    cases Hτ
    case ifz₂ Hτc Hτl Hτr =>
      cases Hτr
      case pure Hτr =>
        apply typing.ifz₂
        apply Hτc; apply Hτl
        apply typing_reification.pure
        rw [← List.nil_append Γ]; apply IH; rfl
        apply Hτr
      case reify Hτr =>
        apply typing.ifz₂
        apply Hτc; apply Hτl
        apply typing_reification.reify
        rw [← List.nil_append Γ]; apply IH; rfl
        apply Hτr

theorem decompose𝔹 :
  ∀ Γ σ B e₀ e₁ τ φ,
    ctx𝔹 B →
    (∀ τ φ,
      typing Γ σ .stat e₀ τ φ →
      typing Γ σ .stat e₁ τ φ
    ) →
    typing Γ σ .stat (B e₀) τ φ →
    typing Γ σ .stat (B e₁) τ φ :=
  by
  intros Γ σ B e₀ e₁ τ φ HB IH Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ IHarg IHf =>
      apply typing.app₁
      apply IH; apply IHf; apply IHarg
  case appr₁ =>
    cases Hτ
    case app₁ IHarg IHf =>
      apply typing.app₁
      apply IHf; apply IH; apply IHarg
  case appl₂ =>
    cases Hτ
    case app₂ IHf IHarg =>
      apply typing.app₂
      apply IH; apply IHf; apply IHarg
  case appr₂ =>
    cases Hτ
    case app₂ IHf IHarg =>
      apply typing.app₂
      apply IHf; apply IH; apply IHarg
  case binaryl₁ =>
    cases Hτ
    case binary₁ IHl IHr =>
      apply typing.binary₁
      apply IH; apply IHl; apply IHr
  case binaryr₁ =>
    cases Hτ
    case binary₁ IHl IHr =>
      apply typing.binary₁
      apply IHl; apply IH; apply IHr
  case binaryl₂ =>
    cases Hτ
    case binary₂ IHl IHr =>
      apply typing.binary₂
      apply IH; apply IHl; apply IHr
  case binaryr₂ =>
    cases Hτ
    case binary₂ IHl IHr =>
      apply typing.binary₂
      apply IHl; apply IH; apply IHr
  case lift =>
    cases Hτ
    case lift_lit IHn =>
      apply typing.lift_lit
      apply IH; apply IHn
    case lift_lam IHe =>
      apply typing.lift_lam
      apply IH; apply IHe
  case lets =>
    cases Hτ
    case lets HwellBinds IHb Hclose IHe =>
      apply typing.lets
      apply IH; apply IHb; apply IHe
      apply HwellBinds; apply Hclose
  case load₁ =>
    cases Hτ
    case load₁ IHe =>
      apply typing.load₁
      apply IH; apply IHe
  case alloc₁ =>
    cases Hτ
    case alloc₁ IHe =>
      apply typing.alloc₁
      apply IH; apply IHe
  case storel₁ =>
    cases Hτ
    case store₁ IHl IHr =>
      apply typing.store₁
      apply IH; apply IHl; apply IHr
  case storer₁ =>
    cases Hτ
    case store₁ IHl IHr =>
      apply typing.store₁
      apply IHl; apply IH; apply IHr
  case load₂ =>
    cases Hτ
    case load₂ IHe =>
      apply typing.load₂
      apply IH; apply IHe
  case alloc₂ =>
    cases Hτ
    case alloc₂ IHe =>
      apply typing.alloc₂
      apply IH; apply IHe
  case storel₂ =>
    cases Hτ
    case store₂ IHl IHr =>
      apply typing.store₂
      apply IH; apply IHl; apply IHr
  case storer₂ =>
    cases Hτ
    case store₂ IHl IHr =>
      apply typing.store₂
      apply IHl; apply IH; apply IHr
  case ifz₁ =>
    cases Hτ
    case ifz₁ IHc IHl IHr =>
      apply typing.ifz₁
      apply IH; apply IHc; apply IHl; apply IHr
  case ifz₂ =>
    cases Hτ
    case ifz₂ IHc IHl IHr =>
      apply typing.ifz₂
      apply IH; apply IHc; apply IHl; apply IHr
  case fix₁ =>
    cases Hτ
    case fix₁ IHe =>
      apply typing.fix₁
      apply IH; apply IHe
  case fix₂ =>
    cases Hτ
    case fix₂ IHe =>
      apply typing.fix₂
      apply IH; apply IHe

theorem decompose𝕄 :
  ∀ Γ σ M e₀ e₁ τ φ,
    ctx𝕄 Γ.length M →
    lc e₀ →
    fv e₁ ⊆ fv e₀ →
    (∀ Γ τ φ,
      typing Γ σ .stat e₀ τ φ →
      typing Γ σ .stat e₁ τ φ
    ) →
    typing Γ σ .stat (M e₀) τ φ →
    typing Γ σ .stat (M e₁) τ φ :=
  by
  intros Γ σ M e₀ e₁ τ φ HM Hlc HFv IH Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HM
  induction HM generalizing τ φ Γ with
  | hole => apply IH; apply Hτ
  | cons𝔹 _ _ HB _ IHM =>
    simp; apply decompose𝔹
    apply HB; intros _ _ IHτ
    apply IHM; apply IHτ; apply HEqlvl; apply Hτ
  | consℝ _ _ HR HM IHM =>
    simp; apply decomposeℝ
    rw [HEqlvl]; apply HR
    apply lc_ctx𝕄
    apply HM; apply Hlc
    . intros _ _ _ _ IHτ
      apply IHM; apply IHτ; simp; omega
    . apply fv_at𝕄; apply HM
      apply HFv
    apply Hτ

theorem decompose𝔼 :
  ∀ Γ σ E e τ φ,
    ctx𝔼 E →
    typing Γ σ .stat (E e) τ φ →
    ∃ τ𝕖 φ𝕖 φ𝔼,
      φ = φ𝕖 ∪ φ𝔼 ∧
      typing Γ σ .stat e τ𝕖 φ𝕖 ∧
      ∀ e φ Δ,
        typing (Δ ++ Γ) σ .stat e τ𝕖 φ →
        typing (Δ ++ Γ) σ .stat (E e) τ (φ ∪ φ𝔼) :=
  by
  intros Γ σ E e τ φ HE Hτ
  induction HE generalizing φ τ with
  | hole =>
    exists τ, φ, ∅
    constructor; cases φ <;> rfl
    constructor; apply Hτ
    intros e φ Δ Hτ; cases φ <;> apply Hτ
  | cons𝔹 _ _ HB _ IH =>
    cases HB
    case appl₁ =>
      cases Hτ
      case app₁ φ₀ φ₁ φ₂ Harg HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₀ ∪ φ𝔼 ∪ φ₂)
        constructor
        . rw [HEqφ]
          cases φ₀ <;> cases φ₂ <;>
          cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₀ ∪ φ𝔼 ∪ φ₂)) = φ₀ ∪ (φ ∪ φ𝔼) ∪ φ₂ :=
            by
            cases φ₀ <;> cases φ₂ <;>
            cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.app₁
          apply IH; apply He
          apply weakening; apply Harg
    case appr₁ =>
      cases Hτ
      case app₁ φ₀ φ₁ φ₂ HX Hf =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₀ ∪ φ₁ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₀ <;> cases φ₁ <;>
          cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₀ ∪ φ₁ ∪ φ𝔼)) = φ₀ ∪ φ₁ ∪ (φ ∪ φ𝔼) :=
            by
            cases φ₀ <;> cases φ₁ <;>
            cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.app₁
          apply weakening; apply Hf
          apply IH; apply He
    case appl₂ =>
      cases Hτ
      case app₂ φ₀ φ₁ HX Harg =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.app₂
          apply IH; apply He
          apply weakening; apply Harg
    case appr₂ =>
      cases Hτ
      case app₂ φ₀ φ₁ Hf HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.app₂
          apply weakening; apply Hf
          apply IH; apply He
    case binaryl₁ =>
      cases Hτ
      case binary₁ φ₀ φ₁ HX Hr =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₁ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₁ <;> cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₁ ∪ φ𝔼)) = ((φ ∪ φ𝔼) ∪ φ₁) :=
            by cases φ₁ <;> cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.binary₁
          apply IH; apply He
          apply weakening; apply Hr
    case binaryr₁ =>
      cases Hτ
      case binary₁ φ₀ φ₁ Hl HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₀ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₀ <;> cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₀ ∪ φ𝔼)) = (φ₀ ∪ (φ ∪ φ𝔼)) :=
            by cases φ₀ <;> cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.binary₁
          apply weakening; apply Hl
          apply IH; apply He
    case binaryl₂ =>
      cases Hτ
      case binary₂ φ₀ φ₁ HX Hr =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.binary₂
          apply IH; apply He
          apply weakening; apply Hr
    case binaryr₂ =>
      cases Hτ
      case binary₂ φ₀ φ₁ Hl HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.binary₂
          apply weakening; apply Hl
          apply IH; apply He
    case lift =>
      cases Hτ
      case lift_lit HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.lift_lit
          apply IH; apply He
      case lift_lam HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.lift_lam
          apply IH; apply He
    case lets =>
      cases Hτ
      case lets body _ _ φ₀ φ₁ HwellBinds HX Hclose Hbody =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₁ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₁ <;> cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₁ ∪ φ𝔼)) = ((φ ∪ φ𝔼) ∪ φ₁) :=
            by cases φ₁ <;> cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.lets
          apply IH; apply He
          rw [← shiftl_id Γ.length body Δ.length]
          rw [← List.singleton_append, ← List.append_assoc]
          rw [List.length_append, Nat.add_comm, ← shiftl_open₀_comm]
          apply weakening_strengthened; apply Hbody; rfl; rfl
          apply Hclose; apply HwellBinds
          apply closed_inc; apply Hclose; simp
    case load₁ =>
      cases Hτ
      case load₁ HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, φ𝔼
        constructor
        . rw [HEqφ]
        . constructor; apply He
          intros e φ Δ He
          apply typing.load₁
          apply IH; apply He
    case alloc₁ =>
      cases Hτ
      case alloc₁ HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, φ𝔼
        constructor
        . rw [HEqφ]
        . constructor; apply He
          intros e φ Δ He
          apply typing.alloc₁
          apply IH; apply He
    case storel₁ =>
      cases Hτ
      case store₁ φ₀ φ₁ HX Hr =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₁ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₁ <;> cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₁ ∪ φ𝔼)) = ((φ ∪ φ𝔼) ∪ φ₁) :=
            by cases φ₁ <;> cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.store₁
          apply IH; apply He
          apply weakening; apply Hr
    case storer₁ =>
      cases Hτ
      case store₁ φ₀ φ₁ Hl HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₀ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₀ <;> cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₀ ∪ φ𝔼)) = (φ₀ ∪ (φ ∪ φ𝔼)) :=
            by cases φ₀ <;> cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.store₁
          apply weakening; apply Hl
          apply IH; apply He
    case load₂ =>
      cases Hτ
      case load₂ HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.load₂
          apply IH; apply He
    case alloc₂ =>
      cases Hτ
      case alloc₂ HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.alloc₂
          apply IH; apply He
    case storel₂ =>
      cases Hτ
      case store₂ φ₀ φ₁ HX Hr =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.store₂
          apply IH; apply He
          apply weakening; apply Hr
    case storer₂ =>
      cases Hτ
      case store₂ φ₀ φ₁ Hl HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.store₂
          apply weakening; apply Hl
          apply IH; apply He
    case ifz₁ =>
      cases Hτ
      case ifz₁ φ₀ φ₁ HX Hl Hr =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₁ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₁ <;> cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₁ ∪ φ𝔼)) = ((φ ∪ φ𝔼) ∪ φ₁) :=
            by cases φ₁ <;> cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.ifz₁
          apply IH; apply He
          apply weakening; apply Hl
          apply weakening; apply Hr
    case ifz₂ =>
      cases Hτ
      case ifz₂ φ₀ φ₁ φ₂ HX Hl Hr =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.ifz₂
          apply IH; apply He
          apply weakening_reification; apply Hl
          apply weakening_reification; apply Hr
    case fix₁ =>
      cases Hτ
      case fix₁ HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, φ𝔼
        constructor
        . rw [HEqφ]
        . constructor; apply He
          intros e φ Δ He
          apply typing.fix₁
          apply IH; apply He
    case fix₂ =>
      cases Hτ
      case fix₂ HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.fix₂
          apply IH; apply He
