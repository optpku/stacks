module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.CompleteDVR.Separated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Proper

/-!
# Noetherian complete DVR criterion for proper morphisms of algebraic spaces
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

/-- If
`f : X ⟶ Y` is a morphism of algebraic spaces over a scheme `S`, `Y` is locally
Noetherian, `f` is of finite type and quasi-separated, and every complete DVR
valuative square admits an extension `A ⊂ A'` of complete discrete valuation
rings with a unique arrow `Spec(A') ⟶ X`, then `f` is proper. -/
instance of_completeDvr {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [FiniteType f] [QuasiSeparated f]
    [ValuativeCriterion.CompleteDVR.Existence f] : Proper f :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
