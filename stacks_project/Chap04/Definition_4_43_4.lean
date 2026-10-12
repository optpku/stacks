/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Monoidal.Invertible

@[expose] public section


universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (X : C)

/- The source defines invertibility through the equivalent criteria of Lemma 4.43.3. The shared
owner `MonoidalCategory.isInvertibleObject` is an `ObjectProperty`, so it can directly form full
monoidal subcategories and support Picard-style constructions; `ExactPairing` and `HasRightDual`
remain data-bearing refinements that choose duality data and impose triangle identities. -/

/- Definition 4.43.4: the canonical predicate expressing that an object `X` of a monoidal
category is invertible is that tensoring on the left by `X` is an equivalence. By Lemma 4.43.3,
this is equivalent to tensoring on the right by `X` being an equivalence and to the existence of
a two-sided tensor inverse for `X`. -/
@[stacks 0FFN "invertible objects via equivalence of left tensoring"]
#check (MonoidalCategory.isInvertibleObject X : Prop)

end CategoryTheory
