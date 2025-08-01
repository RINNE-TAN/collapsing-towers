# Recursion
Our requirement is to have a calculus that can generate second-stage code containing recursion. This way, when discussing the logical equivalence of the generated code, using step indexing becomes meaningful. Generally, there are three ways to implement recursion：
1. fold/unfold
2. Z Combinator
3. Y Combinator
## fold/unfold
## Z Combinator
**Typing Rules**:

$$
\frac{
  \Gamma, \ f : A \to B, \ x : A \vdash e : B
}{
  \Gamma \vdash \text{rec} \ f(x).e : A \to B
}
$$

**Semantic**

$$
(\text{rec} \ f(x).e) v \mapsto [v / x][\text{rec} \ f(x).e / f] e
$$

In the POPL'18 paper, the handling of lift rec is as follows：

$$
\text{lift}(\text{rec} \ f(x).e) \mapsto \text{rec𝕔} \ f(x). [code(x) / x][code(f) / f] e
$$

This only makes sense when the following prerequisites are satisfied:

$$
\frac{
  \Gamma, \ f : \langle A \to B\rangle, \ x : \langle A \rangle \vdash e : \langle B \rangle
}{
  \text{rec} \ f(x).e : \langle A \rangle \to \langle B \rangle
}
$$

and 

$$
\frac{
  \Gamma \vdash e : \langle A \rangle \to \langle B \rangle
}{
  \text{lift}(e) : \langle A \to B \rangle
}
$$

This is contrary to the typing rule of `rec`.
## Y Combinator

**Typing Rules**:

$$
\frac{
  \Gamma \vdash e : A \to A
}{
  \Gamma \vdash \text{fix}(e) : A
}
$$

**Semantic**

$$
\text{fix}(\lambda f. e) \mapsto [\text{fix}(\lambda f. e) / f] e
$$

The problem with the Y combinator is that the object of the `subst` operation is not a value, which causes issues when using logical relations. Consider the fix case of the compatibility lemma:

$$
\frac{
  \Gamma, \ f : A \vDash e : A
}{
  \Gamma \vDash \text{fix}(\lambda f. e) : A
}
$$

Let $\gamma \in \mathcal{G}[\Gamma]$, we must prove that $\gamma(\text{fix}(\lambda f. e)) \in \mathcal{E}[A]$

i.e. $\text{fix}(\lambda f. \gamma(e)) \in \mathcal{E}[A]$

i.e. $[\text{fix}(\lambda f. \gamma(e)) / f] \gamma(e) \in \mathcal{E}[A]$

i.e. $(\gamma \circ [f \mapsto \gamma(\text{fix}(\lambda f. e))])e \in \mathcal{E}[A]$

i.e. $(\gamma \circ [f \mapsto \gamma(\text{fix}(\lambda f. e))]) \in \mathcal{G}[\Gamma, \ f : A]$

i.e. $\gamma(\text{fix}(\lambda f. e)) \in \mathcal{V}[A]$

Here, since our `fix` is indeed not a value, the proof will get stuck. Conversely, if it were, we would find that the proposition we are trying to prove is exactly the same as the original proposition we intended to prove, which can be handled using the `step-indexed` technique.
