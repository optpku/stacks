/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Grp.KanFibration
import StacksCheckRecall

/-!
@stack 08P0

# Lemma 14.31.7 compatibility facade

ReasLib owns the categorical `[Epi f]` fibration instances for simplicial groups and simplicial
abelian groups; termwise surjectivity is a concrete bridge into those owners.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace CategoryTheory.SimplicialObject

variable {X Y : SimplicialObject GrpCat.{u}} (f : X ⟶ Y)
variable {X' Y' : SimplicialObject AddCommGrpCat.{u}} (f' : X' ⟶ Y')

/- Lemma 14.31.7: a termwise-surjective morphism of simplicial abelian groups is a Kan fibration
on underlying simplicial sets. -/
@[stacks 08P0]
#check (AddCommGrp.underlying.fibration.of_surjective f' :
  (∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f'.app n)) →
    Fibration (Functor.whiskerRight f' (forget AddCommGrpCat)))

/- The analogous simplicial-group statement is a reusable generalization of the source entry. -/
#check (Grp.underlying.fibration.of_surjective f :
  (∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) →
    Fibration (Functor.whiskerRight f (forget GrpCat)))

/- Canonical class-shaped formulation, useful after a proof has already established epimorphy. -/
#check Grp.underlying.epi_iff_surjective f
#check AddCommGrp.underlying.epi_iff_surjective f'

variable [Epi f] [Epi f']

#check (inferInstance : Fibration (Functor.whiskerRight f (forget GrpCat)))
#check (inferInstance : Fibration (Functor.whiskerRight f' (forget AddCommGrpCat)))

end CategoryTheory.SimplicialObject
