module

public import stacks_project.Chap88.Lemma_88_22_1_FlatLocus
public import stacks_project.Chap88.Lemma_88_22_1_AffineComparison

/-!
# Lemma 88.22.1

A locally Noetherian formal algebraic space over a complete discrete valuation
ring admits a closed immersion from a flat formal algebraic space through which
every locally Noetherian flat morphism factors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 88.22.1 (1): the morphism from the flat locus of a locally Noetherian
formal algebraic space over a complete discrete valuation ring is a closed
immersion of formal algebraic spaces. -/
@[stacks 0GD8, instance]
instance instClosedImmersion_flatLocusι {S : Scheme.{u}} {A : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) : ClosedImmersion (flatLocusι p) :=
  sorry

/-- Lemma 88.22.1 (2): the flat locus is flat over the complete discrete
valuation ring. -/
@[stacks 0GD8, instance]
instance instFlat_flatLocusToSpf {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) : Flat (flatLocusι p ≫ p) :=
  sorry

/-- Lemma 88.22.1 (3): every morphism from a locally Noetherian formal algebraic
space that is flat over the complete discrete valuation ring factors through
the flat locus. -/
@[stacks 0GD8]
theorem factorsThrough_flatLocus {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) {Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace Y] [IsLocallyNoetherian Y] (g : Y ⟶ X)
    [Flat (g ≫ p)] : lift p g ≫ flatLocusι p = g :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
