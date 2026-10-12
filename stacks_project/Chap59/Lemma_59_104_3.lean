/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_104_1_EtaleSheafDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/-- Lemma 59.104.3: if `f : X ⟶ Y` is a surjective proper morphism of schemes,
then the functor from Type-valued sheaves on `Y.smallEtaleTopology` to singleton
descent data along `{X → Y}`, sending a sheaf to its canonical descent datum, is an
equivalence of categories. -/
@[stacks 0GF0]
theorem descentIsEquivalenceOfSurjectiveProper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [IsProper f] :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.EtaleSheaf
