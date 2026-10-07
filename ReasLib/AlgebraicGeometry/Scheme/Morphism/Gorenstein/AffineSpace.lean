module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.Locus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.NoetherNormalization

/-!
# Gorenstein morphisms and relative affine space

This file characterizes pointwise Gorensteinness using quasi-finite maps to
relative affine space.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a flat, locally finitely presented scheme morphism, being Gorenstein at
 a point is equivalent to Gorensteinness criteria for quasi-finite maps from
 open neighbourhoods into relative affine space of the fibre dimension. -/
theorem gorensteinAt_tfae_affineSpace
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (x : X) (d : ℕ) (hfdim : f.fiberDimensionAt x = (d : WithBot ℕ∞)) :
    let A := AffineSpace (ULift.{u} (Fin d)) S
    List.TFAE [
      f.gorensteinAt x,
      ∃ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ A),
        g ≫ (A ↘ S) = U.ι ≫ f ∧
          LocallyOfFiniteType g ∧ LocallyQuasiFinite g ∧ g.gorensteinAt ⟨x, hxU⟩,
      ∃ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ A),
        g ≫ (A ↘ S) = U.ι ≫ f ∧
          LocallyOfFiniteType g ∧ LocallyQuasiFinite g ∧ AlgebraicGeometry.Gorenstein g,
      ∀ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ A),
        g ≫ (A ↘ S) = U.ι ≫ f →
          FiniteType.QuasiFiniteAt g ⟨x, hxU⟩ → g.gorensteinAt ⟨x, hxU⟩
    ] := sorry

/-- The Gorenstein locus of a flat, locally finitely presented scheme morphism
is open. -/
theorem isOpen_gorensteinLocus_of_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    IsOpen (gorensteinLocus f) := sorry

end AlgebraicGeometry.Scheme.Hom
