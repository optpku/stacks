/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.TwoAffineOpenCover.Smooth
import StacksCheckRecall

/-!
# Smoothness of gluing maps of scheme deformation categories

In Situation 93.9.9, smoothness of `U₁₂ ⟶ Spec(k)` implies smoothness of
`Def_X ⥤ᵇ Def_{U₁} ×_{C_Λ} Def_{U₂}`. If in addition `U₁` is a local complete
intersection over `k`, restriction `Def_X ⥤ᵇ Def_{U₂}` is smooth.

The identifications with the section-ring deformation categories `Def_{P₁}`
and `Def_{P₂}` are the affine deformation equivalences of Lemma 93.9.7.
The product is taken over the Artinian local base category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry BasedFunctor

universe u

/- Lemma 93.16.2
For a two-affine-open cover with smooth intersection, the pair of deformation
restrictions is smooth; if the first open is a local complete intersection,
restriction to the second open is smooth.
-/
@[stacks 0DZN] #check
  (AlgebraicGeometry.Scheme.TwoAffineOpenCover.isSmooth_gluing :
    ∀ (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k] {X : Scheme.{u}} (c : Scheme.TwoAffineOpenCover X)
      (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
      [AlgebraicGeometry.Flat hX]
      [Smooth (Scheme.TwoAffineOpenCover.structureHomInf Λ k c hX)],
      BasedFunctor.IsSmooth (Scheme.TwoAffineOpenCover.toOpenProduct Λ k c hX) ∧
        (Syntomic (Scheme.TwoAffineOpenCover.structureHom₁ Λ k c hX) →
          BasedFunctor.IsSmooth (FlatSchemeCat.restrictOpen Λ k X hX c.U₂)))

