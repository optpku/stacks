/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.Shapes.Pushout.HomEquiv
import StacksCheckRecall

/-!
@stack 016X
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {U V W T : SimplicialObject C}
variable {a : U ⟶ V} {b : U ⟶ W} [HasPushout a b]

/- Lemma 14.8.2: maps from a pushout of simplicial objects are compatible pairs of maps from
its two legs. -/
@[stacks 016X]
#check (pushout.homEquiv a b T :
  (pushout a b ⟶ T) ≃ pushout.CompatiblePair a b T)

#check pushout.homEquiv.apply_inl a b (T := T)
#check pushout.homEquiv.apply_inr a b (T := T)
#check pushout.homEquiv.symm_apply a b (T := T)
#check (fun {S : SimplicialObject C} (h : pushout a b ⟶ S) (k : S ⟶ T) ↦
  pushout.homEquiv.postcomp a b h k)

end CategoryTheory.Limits
