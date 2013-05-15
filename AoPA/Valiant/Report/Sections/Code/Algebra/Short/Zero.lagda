In Agda, we again give the proposition that |0| is a zero element as a conjunction:
\begin{code}
  (∀ x → (0 ∙ x) ≈ 0) 
  ∧ 
  (∀ x → (x ∙ 0) ≈ 0)
\end{code}