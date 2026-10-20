module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.LocalAtTarget

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient

/-- Every scheme-valued base change of the structural morphism of the quotient
of the affine line over a characteristic-zero field by integer translations has
closed projection on points. -/
theorem forallScheme_toBase (k : Type u) [Field k] [CharZero k] :
    AlgebraicGeometry.AlgebraicSpace.Closed.forallScheme
      (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase (space k)) := by
  sorry

/-- The structural morphism of the quotient of the affine line over a
characteristic-zero field by integer translations is universally closed. -/
instance instUniversallyClosed_toBase (k : Type u) [Field k] [CharZero k] :
    AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
      (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase (space k)) :=
  (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.iff_forallScheme _).mpr
    (forallScheme_toBase k)

end AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient
