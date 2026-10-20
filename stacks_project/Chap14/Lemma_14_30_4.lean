module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import StacksCheckRecall

/-!
@stack 08NP

# Lemma 14.30.4 compatibility facade

Composition closure is inherited from the generic right lifting property owner.
-/

@[expose] public section

open CategoryTheory
open SSet.modelCategoryQuillen

universe u

variable {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/- Lemma 14.30.4: the composite of trivial Kan fibrations is a trivial Kan fibration. -/
@[stacks 08NP]
#check (MorphismProperty.comp_mem I.rlp f g : I.rlp f → I.rlp g → I.rlp (f ≫ g))
