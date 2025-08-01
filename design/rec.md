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

**SmallStep Semantic**

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
