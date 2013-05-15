In Agda, given binary operations |_+_| and |_∙_|, we define the proposition that |_∙_| distributes over |_+_|, with respect to a given equivalence relations |_≈_| as the conjunction:
\begin{code}
  (∀ x y z → (x ∙ (y + z)) ≈ ((x ∙ y) + (x ∙ z)))
  ∧ 
  (∀ x y z → ((y + z) ∙ x) ≈ ((y ∙ x) + (z ∙ x)))
\end{code}
We quantify over |x|, |y| and |z| in both conjuncts, to make our code compatible with the Agda Standard Library, and because the two conjuncts make sense as individual propositions, it might be the case that some operation |_∙_| only distributes from the left, for example. Additionally, the parenthesis are needed to guarantee the scoping of |∀|.
