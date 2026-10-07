module

public import ReasLib.AlgebraicGeometry.GeneralLinear.CoordinateRing

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry.GeneralLinear

/-- The determinant of a nonempty finite generic square matrix over a field is irreducible. -/
theorem determinant_irreducible (k : Type u) [Field k] (ι : Type v)
    [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Irreducible (determinant k ι) := sorry

/-- The determinant of the generic `n × n` matrix over a field is irreducible when `0 < n`. -/
theorem determinant_fin_irreducible (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    Irreducible (determinant k (Fin n)) := sorry

end AlgebraicGeometry.GeneralLinear
