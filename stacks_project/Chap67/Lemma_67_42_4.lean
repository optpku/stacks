module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.RingTheory.Valuation.Extension
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap67.Lemma_67_30_5_Flat

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

namespace AlgebraicGeometry.AlgebraicSpace

namespace ofOver

/-- The closed point of `Spec(A)` as a point of the algebraic space associated to a morphism
`Spec (.of A) ⟶ S`. -/
def specClosedPoint {S : Scheme.{u}} {A : Type u} [CommRing A] [IsLocalRing A]
    (σ : Spec (.of A) ⟶ S) : Points (ofOver (Over.mk σ)) :=
  pointsEquiv (Over.mk σ) (IsLocalRing.closedPoint A)

/-- `specClosedPoint σ` is the image of the prime-spectrum closed point under `pointsEquiv`. -/
theorem specClosedPoint_eq {S : Scheme.{u}} {A : Type u} [CommRing A] [IsLocalRing A]
    (σ : Spec (.of A) ⟶ S) :
    specClosedPoint σ = pointsEquiv (Over.mk σ) (IsLocalRing.closedPoint A) :=
  sorry

end ofOver

namespace Flat

/-- Lemma 67.42.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of algebraic
spaces over `S`. Let `Spec(A) ⟶ Y` be a morphism where `A` is a valuation ring. If the
closed point of `Spec(A)` maps to a point of `|Y|` in the image of `|X| ⟶ |Y|`, then there
exists a commutative square `Spec(A') ⟶ X` over `Spec(A) ⟶ Y` where `A → A'` is an
extension of valuation rings in the sense of `IsExtensionOfValuationRings`. -/
@[stacks 089F]
theorem exists_isExtensionOfValuationRings {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Flat f] {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (σ : Spec (.of A) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y)
    (h_image : Points.map g (ofOver.specClosedPoint σ) ∈ Set.range (Points.map f)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : ValuationRing A')
      (_ : Algebra A A') (_ : IsExtensionOfValuationRings A A')
      (lift : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ σ)) ⟶ X),
      CommSq lift (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A A'))) rfl) f g :=
  sorry

/-- The same lifting property, with commutativity packaged as an equality of composites. -/
theorem exists_isExtensionOfValuationRings_fac {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Flat f] {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (σ : Spec (.of A) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y)
    (h_image : Points.map g (ofOver.specClosedPoint σ) ∈ Set.range (Points.map f)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : ValuationRing A')
      (_ : Algebra A A') (_ : IsExtensionOfValuationRings A A')
      (lift : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ σ)) ⟶ X),
      lift ≫ f =
        ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A A'))) rfl ≫ g :=
  sorry

end Flat

end AlgebraicGeometry.AlgebraicSpace
