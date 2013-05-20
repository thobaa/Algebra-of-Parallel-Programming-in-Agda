In Agda, we give the proposition that |z| is a zero element as the conjunction
\begin{code}
(∀ x → (z ∙ x) ≈ z) ∧ (∀ x → (x ∙ z) ≈ z)
\end{code}
