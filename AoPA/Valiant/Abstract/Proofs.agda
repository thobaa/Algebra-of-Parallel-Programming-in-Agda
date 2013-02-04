{-splitUnsplit : ∀ {m n} → (A : Matrix m n) → (splitR : Fin m) → (splitC : Fin n) → (i : Fin m) → (j : Fin n) → A i j ≡ Four' {rSplit = splitR} {cSplit = splitC} (UL A splitR splitC) (UR A splitR (fsuc splitC)) (LL A (fsuc splitR) splitC ) (LR A (fsuc splitR) (fsuc splitC)) i j
splitUnsplit {m} {n} A splitR splitC i j = {!!}-}
