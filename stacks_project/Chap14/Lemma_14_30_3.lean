/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import StacksCheckRecall

/-!
@stack 08NN

# Lemma 14.30.3 compatibility facade

Stability of a trivial Kan fibration under pullback is the generic base-change theorem for the
right lifting property against boundary inclusions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

universe u

variable {X Y Y' : SSet.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}

/- Lemma 14.30.3: trivial Kan fibrations are stable under base change. -/
@[stacks 08NN]
#check (I.rlp.pullback_snd f g : I.rlp f → I.rlp (pullback.snd f g))
