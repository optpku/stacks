module

public import ReasLib.AlgebraicGeometry.GeneralLinear.Irreducibility
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

/- Lemma 43.23.7: over a field, the determinant of the generic `n × n` matrix is
irreducible in the polynomial ring on its entries when `0 < n`. -/
@[stacks 0B2V] #check
  (AlgebraicGeometry.GeneralLinear.determinant_fin_irreducible :
    ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
      Irreducible (AlgebraicGeometry.GeneralLinear.determinant k (Fin n)))
