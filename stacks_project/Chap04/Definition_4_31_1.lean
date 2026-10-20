/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Biterminal
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open scoped Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]
variable (x : B)

/- Definition 4.31.1: an object `x` is final in a `(2, 1)`-category when every object admits a
`1`-morphism to `x` and every two such morphisms are related by a unique `2`-isomorphism. The
biequivalence-invariant owner is `Bicategory.IsBiterminal`. -/
@[stacks 003P "final object via contractible hom-categories"]
#check (Bicategory.IsBiterminal x : Prop)

/- The source existence-and-uniqueness formulation is the canonical characterization of a
biterminal object. -/
@[stacks 003P "existence and unique 2-morphism characterization"]
#check (Bicategory.isBiterminal_iff_existsUnique_hom₂ x :
  Bicategory.IsBiterminal x ↔
    ∀ y : B, Nonempty (y ⟶ x) ∧
      ∀ f g : y ⟶ x, Nonempty (f ⟶ g) ∧ Subsingleton (f ⟶ g))

end CategoryTheory
