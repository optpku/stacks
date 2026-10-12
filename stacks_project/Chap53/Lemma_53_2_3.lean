/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Curve.Flat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 53.2.3: a nonconstant morphism of curves over a field with normal target is flat. -/
@[stacks 0CCK] #check
  (AlgebraicGeometry.Scheme.Hom.IsNonconstant.flat_of_curves :
    ∀ {k : Type u} [Field k] {X Y : Over (Spec (CommRingCat.of k))}
      [Curve X] [Curve Y] {f : X ⟶ Y} (hf : f.left.IsNonconstant)
      (hY : Y.left.isNormal),
      Flat f.left)
