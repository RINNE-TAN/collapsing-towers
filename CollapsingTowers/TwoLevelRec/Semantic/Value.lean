import CollapsingTowers.TwoLevelRec.Syntax.Defs

inductive value : Expr → Prop where
  | lam : ∀ e, lc (.lam e) → value (.lam e)
  | lit : ∀ n, value (.lit n)
  | code : ∀ e, lc e → value (.code e)

lemma lc.value : ∀ e, value e → lc e := by
  intro e Hvalue
  cases Hvalue with
  | lam _ Hclosed => apply Hclosed
  | lit => constructor
  | code _ Hclosed => apply Hclosed

instance lc_at.decidable (e : Expr) (i : Nat) : Decidable (lc_at e i) :=
  match e with
  | .bvar j => if h : j < i then isTrue h else isFalse h
  | .fvar _ => isTrue (by simp)
  | .lam e => lc_at.decidable e (i + 1)
  | .lift e => lc_at.decidable e i
  | .app₁ f arg =>
    match lc_at.decidable f i, lc_at.decidable arg i with
    | isTrue Hf, isTrue Ha => isTrue ⟨Hf, Ha⟩
    | isFalse Hf, _ => isFalse (λ H => Hf H.left)
    | _, isFalse Ha => isFalse (λ H => Ha H.right)
  | .app₂ f arg =>
    match lc_at.decidable f i, lc_at.decidable arg i with
    | isTrue Hf, isTrue Ha => isTrue ⟨Hf, Ha⟩
    | isFalse Hf, _ => isFalse (λ H => Hf H.left)
    | _, isFalse Ha => isFalse (λ H => Ha H.right)
  | .lit _ => isTrue (by simp)
  | .run e => lc_at.decidable e i
  | .code e => lc_at.decidable e i
  | .reflect e => lc_at.decidable e i
  | .lam𝕔 e => lc_at.decidable e (i + 1)
  | .lets b e =>
    match lc_at.decidable b i, lc_at.decidable e (i + 1) with
    | isTrue Hb, isTrue He => isTrue ⟨Hb, He⟩
    | isFalse Hb, _ => isFalse (λ H => Hb H.left)
    | _, isFalse He => isFalse (λ H => He H.right)
  | .lets𝕔 b e =>
    match lc_at.decidable b i, lc_at.decidable e (i + 1) with
    | isTrue Hb, isTrue He => isTrue ⟨Hb, He⟩
    | isFalse Hb, _ => isFalse (λ H => Hb H.left)
    | _, isFalse He => isFalse (λ H => He H.right)
  | .fix₁ e => lc_at.decidable e i
  | .fix₂ e => lc_at.decidable e i

instance value.decidable (e : Expr) : Decidable (value e) :=
  match e with
  | .lam e =>
    match lc_at.decidable e 1 with
    | isTrue Hlc => isTrue (by apply value.lam; apply Hlc)
    | isFalse Hlc => isFalse (by intros Hvalue; apply Hlc; apply lc.value _ Hvalue)
  | .lit _ => isTrue (by apply value.lit)
  | .code e =>
    match lc_at.decidable e 0 with
    | isTrue Hlc => isTrue (by apply value.code; apply Hlc)
    | isFalse Hlc => isFalse (by intros Hvalue; apply Hlc; apply lc.value _ Hvalue)
  | .bvar j => isFalse (by intros Hvalue; nomatch Hvalue)
  | .fvar _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .lift e => isFalse (by intros Hvalue; nomatch Hvalue)
  | .app₁ f arg => isFalse (by intros Hvalue; nomatch Hvalue)
  | .app₂ f arg => isFalse (by intros Hvalue; nomatch Hvalue)
  | .run e => isFalse (by intros Hvalue; nomatch Hvalue)
  | .reflect e => isFalse (by intros Hvalue; nomatch Hvalue)
  | .lam𝕔 e => isFalse (by intros Hvalue; nomatch Hvalue)
  | .lets b e => isFalse (by intros Hvalue; nomatch Hvalue)
  | .lets𝕔 b e => isFalse (by intros Hvalue; nomatch Hvalue)
  | .fix₁ e => isFalse (by intros Hvalue; nomatch Hvalue)
  | .fix₂ e => isFalse (by intros Hvalue; nomatch Hvalue)
