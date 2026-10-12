/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.25.3: let `f : X ⟶ Spec(k)` be a smooth morphism where `k` is a field. Then `X` is
a regular scheme. -/
@[stacks 056S] #check
  (AlgebraicGeometry.Scheme.Hom.regular_of_smooth_over_field :
    {k : Type u} → [Field k] → {X : AlgebraicGeometry.Scheme.{u}} →
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) →
        [AlgebraicGeometry.Smooth f] → AlgebraicGeometry.Scheme.Regular X)
