/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.DimensionOne
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.43.4: let `X` be a proper scheme over a field `k`. If
`topologicalKrullDim X ≤ 1`, then the structure morphism `f : X ⟶ Spec (CommRingCat.of k)` is
H-projective. -/
@[stacks 0A26] #check
  (AlgebraicGeometry.HProjective.of_dimension_le_one :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
      topologicalKrullDim X ≤ 1 → HProjective f)
