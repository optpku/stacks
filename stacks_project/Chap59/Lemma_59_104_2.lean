/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/- Lemma 59.104.2: if `f : X ⟶ Y` is a surjective integral morphism of schemes,
then the functor from Type-valued sheaves on `Y.smallEtaleTopology` to singleton
descent data along `{X → Y}`, sending a sheaf to its canonical descent datum, is an
equivalence of categories. -/
@[stacks 0GEZ] #check
  (AlgebraicGeometry.Scheme.EtaleSheaf.descentIsEquivalenceOfSurjectiveIntegral :
    {X Y : Scheme.{u}} → (f : X ⟶ Y) → [Surjective f] → [IsIntegralHom f] →
      (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence)

end AlgebraicGeometry.Scheme.EtaleSheaf
