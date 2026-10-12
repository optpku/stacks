/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 30.26.4: in a cartesian diagram of schemes
`X' ⟶ X` over `S' ⟶ S`, if `f : X ⟶ S` is locally of finite type and a closed subset
`Z ⊆ X` is proper over `S`, then its inverse image in `X'` is proper over `S'`. -/
@[stacks 0CYP] #check
  (AlgebraicGeometry.ClosedSubset.IsProperOver.preimage :
    ∀ {X' X S' S : AlgebraicGeometry.Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
      {f : X ⟶ S} {g : S' ⟶ S} (sq : IsPullback g' f' f g)
      [AlgebraicGeometry.LocallyOfFiniteType f] (Z : TopologicalSpace.Closeds X)
      [AlgebraicGeometry.ClosedSubset.IsProperOver f Z],
      AlgebraicGeometry.ClosedSubset.IsProperOver f' (Z.preimage g'.continuous))
