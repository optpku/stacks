module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.Adjunction

/-!
# Identity-base étale relocalization

The identity-base relocalization sends an étale scheme over an algebraic space
to the same object of the big étale slice site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

/-- Relocalization of the identity morphism sends a scheme étale over `X` to the
same object of `Over X`. -/
theorem relocalizationFunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    (relocalizationFunctor (𝟙 X)).obj U = Over.mk U.hom := sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
