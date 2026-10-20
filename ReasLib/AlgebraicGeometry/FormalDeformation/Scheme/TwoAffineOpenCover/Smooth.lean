/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.TwoAffineOpenCover.Pair
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic

/-!
# Smoothness of gluing maps of scheme deformation categories

For two affine opens with smooth affine intersection, the pair of deformation
restrictions is smooth. If the first open is a local complete intersection,
restriction to the second open is smooth as well.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

universe u

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X : Scheme.{u}} (c : TwoAffineOpenCover X)
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable [AlgebraicGeometry.Flat hX]

/-- For a scheme covered by two affine opens with smooth affine intersection,
the pair of deformation restrictions is smooth. If the first open is a local
complete intersection over the residue field, restriction to the second open
is smooth. -/
theorem isSmooth_gluing [Smooth (structureHomInf Λ k c hX)] :
    BasedFunctor.IsSmooth (toOpenProduct Λ k c hX) ∧
      (Syntomic (structureHom₁ Λ k c hX) →
        BasedFunctor.IsSmooth (FlatSchemeCat.restrictOpen Λ k X hX c.U₂)) :=
  sorry

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
