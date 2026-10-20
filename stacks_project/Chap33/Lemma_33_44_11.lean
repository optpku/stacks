/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.44.11: let `k` be a field, let `f : X ⟶ Y` be a nonconstant morphism of
proper curves over `k`, and let `ℰ` be a finite locally free `𝒪_Y`-module. Then
`deg(f^*ℰ) = deg(X/Y) * deg(ℰ)`. -/
@[stacks 0AYZ] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree_pullback_eq_inducedFunctionFieldDegree_mul :
    ∀ {k : Type u} [Field k] {X Y : Over (Spec (CommRingCat.of k))}
      [Curve X] [Curve Y] [IsProper X.hom] [IsProper Y.hom]
      (f : X ⟶ Y) [IsDominant f.left] (ℰ : Y.left.Modules) [Scheme.Modules.IsFiniteLocallyFree ℰ],
      Scheme.Modules.curveDegreeOfFiniteLocallyFree
          ((Scheme.Modules.pullback f.left).obj ℰ) =
        (f.left.inducedFunctionFieldDegree : ℤ) *
          Scheme.Modules.curveDegreeOfFiniteLocallyFree ℰ)
