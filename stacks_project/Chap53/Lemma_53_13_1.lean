/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Curve.Smooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 53.13.1 -/
@[stacks 0CCW] #check
  (AlgebraicGeometry.Scheme.Hom.smooth_of_surjective_of_normal :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} [Curve X] [Curve Y]
      (f : X ⟶ Y) [Surjective f.left] [Smooth X.hom] (hY : Y.left.isNormal),
      Smooth Y.hom)
