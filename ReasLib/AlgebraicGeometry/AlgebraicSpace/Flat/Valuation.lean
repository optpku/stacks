module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.RingTheory.Valuation.Extension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Lifting valuation rings through flat morphisms of algebraic spaces

A flat morphism of algebraic spaces lifts a valuation-ring point of the target after an
extension of valuation rings, provided the closed point of the source spectrum lands in the
image of the map on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flat

/-- Let `S` be a scheme and `f : X ⟶ Y` a flat morphism of algebraic spaces over `S`.
A morphism `Spec(A) ⟶ Y` from a valuation ring lifts to `X` after an extension of
valuation rings whenever its closed point lies in the image of the map on points of `f`.
The lift forms a commutative square with the canonical morphism of spectra. -/
@[stacks 089F]
theorem exists_isExtensionOfValuationRings {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Flat f] {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (σ : Spec (.of A) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y)
    (h_image : Points.map g (ofOver.pointsEquiv (Over.mk σ) (IsLocalRing.closedPoint A)) ∈
      Set.range (Points.map f)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : ValuationRing A')
      (_ : Algebra A A') (_ : IsExtensionOfValuationRings A A')
      (lift : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ σ)) ⟶ X),
      CommSq lift (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A A'))) rfl) f g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Flat
