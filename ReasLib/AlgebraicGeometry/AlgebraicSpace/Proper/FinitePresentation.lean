module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.FinitePresentation

/-!
# Finite-presentation and étale affine-space tests for proper morphisms

A separated finite-type morphism of algebraic spaces is proper precisely when
its locally finitely presented base changes are closed, or when all affine-space
tests are closed after passage to a surjective étale scheme atlas of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] [FiniteType f]

/-- For a separated finite-type morphism of algebraic spaces over a scheme,
properness, closedness of every locally finitely presented base change, and
closedness of all affine-space product projections after passage to some
surjective étale scheme atlas of the target are equivalent. -/
theorem tfae_separatedFiniteType :
    List.TFAE [Proper f, Closed.forallLocallyOfFinitePresentation f,
      Closed.existsEtaleAffineSpace f] := sorry

/-- A separated finite-type morphism of algebraic spaces is proper iff every
base change along a morphism locally of finite presentation has closed
projection on points. -/
theorem iff_forallLocallyOfFinitePresentation :
    Proper f ↔ Closed.forallLocallyOfFinitePresentation f := sorry

/-- A separated finite-type morphism of algebraic spaces is proper iff some
surjective étale scheme atlas of the target has closed affine-space product
projections. -/
theorem iff_existsEtaleAffineSpace :
    Proper f ↔ Closed.existsEtaleAffineSpace f := sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
