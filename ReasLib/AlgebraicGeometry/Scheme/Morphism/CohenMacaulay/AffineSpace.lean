/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.NoetherNormalization

/-!
# Cohen--Macaulay morphisms and relative affine space

This file characterizes pointwise Cohen--Macaulayness using quasi-finite maps
to relative affine space.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a flat, locally finitely presented scheme morphism, being Cohen--Macaulay
at a point is equivalent to flatness criteria for quasi-finite maps from open
neighbourhoods into relative affine space of the fibre dimension. -/
theorem cohenMacaulayAt_tfae_affineSpace
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (x : X) (d : ℕ) (hfdim : f.fiberDimensionAt x = (d : WithBot ℕ∞)) :
    let A := AffineSpace (ULift.{u} (Fin d)) S
    List.TFAE [
      f.CohenMacaulayAt x,
      ∃ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ A),
        g ≫ (A ↘ S) = U.ι ≫ f ∧
          LocallyOfFiniteType g ∧ LocallyQuasiFinite g ∧ g.flatAt ⟨x, hxU⟩,
      ∃ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ A),
        g ≫ (A ↘ S) = U.ι ≫ f ∧
          LocallyOfFiniteType g ∧ LocallyQuasiFinite g ∧ Flat g,
      ∀ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ A),
        g ≫ (A ↘ S) = U.ι ≫ f →
          FiniteType.QuasiFiniteAt g ⟨x, hxU⟩ → g.flatAt ⟨x, hxU⟩
    ] := sorry

end AlgebraicGeometry.Scheme.Hom
