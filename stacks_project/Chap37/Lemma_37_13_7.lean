/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.NaiveCotangent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 37.13.7: a scheme morphism is smooth exactly when it is locally of finite
presentation, its degree `-1` naive-cotangent homology is zero, and its relative
differentials are finite locally free. -/
@[stacks 0D0N]
#check (AlgebraicGeometry.Smooth.iff_naiveCotangent :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    Smooth f ↔ LocallyOfFinitePresentation f ∧
      IsZero ((NL[f.toShHom]).homology (-1)) ∧
        (Ω[f.toShHom]).IsFiniteLocallyFree)
