module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_16_6_SchemeTheoreticImage

/-!
# Valuative realization of points of scheme-theoretic images

A point of the scheme-theoretic image of a quasi-compact morphism of algebraic
spaces is realized by a valuation ring whose generic point lifts to the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage

/-- Lemma 67.16.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact morphism
of algebraic spaces over `S`. Let `Z` be the scheme-theoretic image of `f`. Let
`z : Points Z`. There exists a valuation ring `A` with fraction field `K` and a
commutative diagram `Spec (.of K) ⟶ X` over `Spec (.of A) ⟶ Z ⟶ Y` such that the
closed point of `Spec (.of A)` maps to `z`. -/
@[stacks 089B]
theorem exists_valuationRing_diagram {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [QuasiCompact f] [IsSchemeTheoreticImage f toImage ι] (z : Points Z) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
      (σ : Spec (.of A) ⟶ S)
      (genericToX :
        ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ σ)) ⟶ X)
      (valuationToImage : ofOver (Over.mk σ) ⟶ Z),
      CommSq genericToX (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl)
          toImage valuationToImage ∧
        Points.mapOfOver valuationToImage (IsLocalRing.closedPoint A) = z := sorry

/-- The same valuative realization, with commutativity of the left square packaged as
an equality of composites. -/
theorem exists_valuationRing_diagram_fac {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [QuasiCompact f] [IsSchemeTheoreticImage f toImage ι] (z : Points Z) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
      (σ : Spec (.of A) ⟶ S)
      (genericToX :
        ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ σ)) ⟶ X)
      (valuationToImage : ofOver (Over.mk σ) ⟶ Z),
      genericToX ≫ toImage =
          ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl ≫
            valuationToImage ∧
        Points.mapOfOver valuationToImage (IsLocalRing.closedPoint A) = z := sorry

end AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage
