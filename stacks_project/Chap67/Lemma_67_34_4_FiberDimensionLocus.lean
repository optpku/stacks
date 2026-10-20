module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Locus

/-!
# Bounded fibre-dimension loci of morphisms of algebraic spaces

The set of points of an algebraic space at which a morphism has relative
dimension at most a given natural number, together with membership and
étale-preimage comparisons to the scheme-level locus.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.fiberDimensionLELocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (n : ℕ), Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.mem_fiberDimensionLELocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (n : ℕ) (x : Points X),
    x ∈ fiberDimensionLELocus f n ↔
      fiberDimensionAt f x ≤ (n : WithBot ℕ∞))

#check (AlgebraicGeometry.AlgebraicSpace.mem_fiberDimensionLELocus_iff_relativeDimensionLEAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (n : ℕ)
    (x : Points X),
    x ∈ fiberDimensionLELocus f n ↔ RelativeDimensionLEAt f n x)

#check (AlgebraicGeometry.AlgebraicSpace.mapOfOver_preimage_fiberDimensionLELocus :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (n : ℕ) {U V : Over S}
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b),
    Points.mapOfOver a ⁻¹' fiberDimensionLELocus f n =
      Scheme.Hom.fiberDimensionLELocus h.left n)
