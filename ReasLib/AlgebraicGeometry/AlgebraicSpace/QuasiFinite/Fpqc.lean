module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage

/-!
# Quasi-finiteness is fpqc local on the target

The conjunction of local finite type and chartwise local quasi-finiteness, and
quasi-finiteness, are local on the target for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FiniteType

/-- The conjunction of local finite type and chartwise local quasi-finiteness
for morphisms of algebraic spaces is local on the target for the fpqc
precoverage. The local finite type condition supplies the finite-type convention
for locally quasi-finite morphisms. -/
instance locallyQuasiFinite_isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FiniteType

namespace AlgebraicGeometry.AlgebraicSpace.QuasiFinite

/-- Quasi-finiteness of morphisms of algebraic spaces, including finite type
and chartwise local quasi-finiteness, is local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@QuasiFinite S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QuasiFinite
