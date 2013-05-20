In Agda, given binary operations |_+_| and |_∙_|, we define the proposition that |_∙_| distributes over |_+_|, with respect to a given equivalence relations |_≈_| as the conjunction:
\begin{code}
  (∀ x y z → (x ∙ (y + z)) ≈ ((x ∙ y) + (x ∙ z)))
  ∧ 
  (∀ x y z → ((y + z) ∙ x) ≈ ((y ∙ x) + (z ∙ x)))
\end{code}
