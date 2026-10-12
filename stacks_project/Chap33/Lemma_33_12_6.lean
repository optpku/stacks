/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 33.12.6: geometric regularity at a point is equivalent to smoothness there. -/
@[stacks 038X] #check
  (AlgebraicGeometry.Scheme.Hom.geometricallyRegularAt_iff_smoothAt :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (x : X),
      Scheme.Hom.IsGeometricallyRegularAt f x ↔ f.SmoothAt x)

end AlgebraicGeometry
