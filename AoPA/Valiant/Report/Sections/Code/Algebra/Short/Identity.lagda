\begin{code}
(∀ x → (e ∙ x) ≈ x) ∧ (∀ x → (x ∙ e) ≈ x)
\end{code}
We quantify over |x| in both conjuncts to make our code compatible with the Agda Standard Library and because the two conjuncts make sense as individual propositions. It might be the case that some element |e| is only an inverse of |_∙_| when multiplied on the left, for example. The parentheses in the type are needed to give |∀| the correct scope.
