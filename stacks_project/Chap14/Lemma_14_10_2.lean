/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.Shapes.Pullback.HomEquiv
import StacksCheckRecall

/-!
@stack 0173
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {T U V W : CosimplicialObject C}
variable (a : V ⟶ U) (b : W ⟶ U) [HasPullback a b]

/- Lemma 14.10.2: maps into a pullback of cosimplicial objects are compatible pairs of maps into
its two legs. -/
@[stacks 0173]
#check (pullback.homEquiv a b T :
  (T ⟶ pullback a b) ≃ pullback.CompatiblePair a b T)

#check pullback.homEquiv.apply_fst a b (T := T)
#check pullback.homEquiv.apply_snd a b (T := T)
#check pullback.homEquiv.symm_apply a b (T := T)
#check (fun {S : CosimplicialObject C} (k : S ⟶ T) (h : T ⟶ pullback a b) ↦
  pullback.homEquiv.precomp a b k h)

end CategoryTheory.Limits
