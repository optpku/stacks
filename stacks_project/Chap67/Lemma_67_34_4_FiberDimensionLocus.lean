module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
public import stacks_project.Chap67.Lemma_67_34_3_FiberDimension

/-!
# Bounded fibre-dimension loci of morphisms of algebraic spaces

The set of points of an algebraic space at which a morphism has relative
dimension at most a given natural number, together with membership and
étale-preimage comparisons to the scheme-level locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The locus of points of `X` at which a morphism `f : X ⟶ Y` of algebraic
spaces has relative dimension at most `n`. -/
noncomputable def fiberDimensionLELocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (n : ℕ) : Set (Points X) :=
  {x | fiberDimensionAt f x ≤ (n : WithBot ℕ∞)}

/-- Membership in `fiberDimensionLELocus f n` is the bound
`fiberDimensionAt f x ≤ n`. -/
theorem mem_fiberDimensionLELocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (n : ℕ) (x : Points X) :
    x ∈ fiberDimensionLELocus f n ↔
      fiberDimensionAt f x ≤ (n : WithBot ℕ∞) :=
  sorry

/-- Membership in `fiberDimensionLELocus f n` is the source predicate that `f`
has relative dimension at most `n` at `x`. -/
theorem mem_fiberDimensionLELocus_iff_relativeDimensionLEAt
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (n : ℕ)
    (x : Points X) :
    x ∈ fiberDimensionLELocus f n ↔ RelativeDimensionLEAt f n x :=
  sorry

/-- Along an étale scheme square over `f`, the preimage of
`fiberDimensionLELocus f n` is the scheme-level fibre-dimension locus of the
top arrow. -/
theorem mapOfOver_preimage_fiberDimensionLELocus {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (n : ℕ) {U V : Over S}
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) :
    Points.mapOfOver a ⁻¹' fiberDimensionLELocus f n =
      Scheme.Hom.fiberDimensionLELocus h.left n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
