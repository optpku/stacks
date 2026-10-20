/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Pullback
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Definition 8.3.4: with `𝒰 = {U_i ⟶ U}_{i ∈ I}`, `𝒱 = {V_j ⟶ V}_{j ∈ J}`, an index map
`α : I → J`, a base morphism `h : U ⟶ V`, and component maps `g_i : U_i ⟶ V_{α(i)}` as in Lemma
8.3.3, the functor
`(Y_j, φ_{jj'}) ↦ (g_i* Y_{α(i)}, (g_i × g_{i'})* φ_{α(i)α(i')})`
constructed there is the pullback functor on descent data. -/
@[stacks 02ZE "pullback of family descent data"]
#check @DescentDatum.Pullback.functor

#check @DescentDatum.Pullback.functor_obj_obj

#check @DescentDatum.Pullback.functor_map_hom

#check @DescentDatum.Pullback.functor_obj_hom

end CategoryTheory
