module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType

/-!
# Bounded fibre-dimension loci of morphisms of algebraic spaces

The relative-dimension sublevel sets are compatible with étale scheme squares.
For locally finite-type morphisms, these sets are open in the canonical topology
on points.
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

/-- A point belongs to `fiberDimensionLELocus f n` if and only if `f` has
relative dimension at most `n` at that point. -/
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

/-- For a locally finite-type morphism of algebraic spaces, the locus where
the relative dimension is at most `n` is open in the canonical topology on
source points. -/
theorem isOpen_fiberDimensionLELocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (n : ℕ)
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ) :
    @IsOpen (Points X) τ (fiberDimensionLELocus f n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
