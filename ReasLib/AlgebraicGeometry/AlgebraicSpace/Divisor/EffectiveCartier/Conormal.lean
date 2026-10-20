module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.IdealComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.AssociatedSheaf

/-!
# Conormal sheaves of effective Cartier divisors

The conormal sheaf of an effective Cartier divisor is the restriction of its
negative divisor sheaf, equivalently its ideal sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom.Conormal

/-- The canonical comparison from the restricted ideal sheaf of an effective
Cartier divisor to its conormal sheaf is an isomorphism. The ideal sheaf is the
negative divisor sheaf, equivalently the tensor inverse of the associated
divisor sheaf. -/
@[instance]
theorem pullbackIdealComparison_isIso {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] :
    IsIso
      (pullbackIdealComparison i :
        (Modules.pullback i).obj (negSheaf i) ⟶ conormalSheaf i) :=
  sorry

end Hom.Conormal

end AlgebraicGeometry.AlgebraicSpace
