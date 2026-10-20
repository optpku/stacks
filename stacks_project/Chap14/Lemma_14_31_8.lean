/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.TrivialKanFibration
import StacksCheckRecall

/-!
@stack 08P1

# Lemma 14.31.8 compatibility facade

ReasLib separates the generic acyclic-kernel statement, the symmetric comparison between the two
Dold--Kan chain-complex conventions, and the simplicial-abelian-group lifting criterion.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology AlgebraicTopology.DoldKan
open SSet.modelCategoryQuillen

universe u

namespace CategoryTheory.SimplicialObject.AddCommGrp.underlying

variable {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)

/- Lemma 14.31.8: a termwise surjective quasi-isomorphism of simplicial abelian groups is a trivial
Kan fibration on underlying simplicial sets. -/
@[stacks 08P1]
#check (trivialKanFibrations.alternatingFace.of_surjective (f := f) :
  (∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) →
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f) →
      I.rlp (Functor.whiskerRight f (forget AddCommGrpCat)))

#check trivialKanFibrations.normalizedMoore.of_surjective (f := f)
#check trivialKanFibrations.normalizedMoore
#check trivialKanFibrations.alternatingFace

end CategoryTheory.SimplicialObject.AddCommGrp.underlying
