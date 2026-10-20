/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Homology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{max w v}]

/- Definition 25.4.1: the homology sheaves of a simplicial presheaf are owned by the neutral
site-level free-abelian sheaf complex construction. -/
@[stacks 01GB] #check @SimplicialPresheaf.Homology.functor

/- The reusable construction includes its degreewise free-abelian sheaf, associated complex,
and functorial homology-map APIs. -/
#check SimplicialPresheaf.Homology.complexFunctor
#check SimplicialPresheaf.Homology.complexFunctor_obj
#check SimplicialPresheaf.Homology.complexFunctor_map
#check SimplicialPresheaf.Homology.functor_obj
#check SimplicialPresheaf.Homology.functor_map

end CategoryTheory
