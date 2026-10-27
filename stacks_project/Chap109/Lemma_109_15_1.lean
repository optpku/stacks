/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.SourceSmoothLocus
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Functor
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

/- Lemma 109.15.1: a proper scheme of dimension at most one over a field lies
in the smooth source locus of the stack of curves if and only if its deformation
category is unobstructed, expressed after flat coefficient base change. -/
@[stacks 0DZU] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_sourceSmoothLocus_iff_unobstructed :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (Λ : Type u)
    [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ k] [Module.Finite Λ k]
    [Module.Flat ℤ Λ],
    sourceSmoothLocus (Spec (CommRingCat.of Λ))
        (mkOverCoefficient X hdim Λ) ↔
      Functor.IsUnobstructed
        (Over.forget (Fiber.fiberInclusion.obj
            (FlatSchemeCat.residueObj Λ k X.left X.hom)) ⋙
          FlatSchemeCat.forget Λ k))
