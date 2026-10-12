/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Ample
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.44.14: let `k` be a field, let `X` be a proper curve over `k`, and let `ℒ` be an
invertible `𝒪_X`-module. Then `ℒ` is ample if and only if its degree is positive. -/
@[stacks 0B5X]
#check
  (AlgebraicGeometry.Scheme.Modules.isAmple_iff_curveDegreeOfInvertible_pos :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
      (ℒ : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ],
      AlgebraicGeometry.Scheme.Modules.IsAmple ℒ ↔
        0 < AlgebraicGeometry.Scheme.Modules.curveDegreeOfInvertible
          X.hom (topologicalKrullDim_eq_one X).le ℒ)
