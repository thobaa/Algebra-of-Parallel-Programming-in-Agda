%if False
\begin{code}
module CH where
\end{code}
%endif
\subsection{The Curry Howard Correspondence}
To define a conjunction between two Propositions |P| and |Q|, one uses the pair |P × Q| defined below
\begin{code}
data _×_ (P Q : Set) : Set where  
  _,_ : (p : P) → (q : Q) → P × Q
\end{code}
Because, to construct an element of |P × Q|, one needs an element of both |P| and |Q|.

For disjunction, one uses the disjoint sum |P + Q|:
\begin{code}

\end{code}
For implication, functions
\begin{code}
  
\end{code}
For universal quantification, 

For existential quantification, 
