/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms of stacks in groupoids

This file lifts isomorphisms of groupoid-fibred categories to the bundled stack layer and
records the forward and inverse computation rules.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Groupoids

variable {J : GrothendieckTopology C}

namespace isoOfGroupoids

/-- Lifting the two directions of a groupoid-fibred isomorphism satisfies the first inverse
law. -/
@[stacks 02ZK "forward inverse law for lifted groupoid-stack isomorphisms"]
theorem hom_comp_inv {X Y : StackOver.Groupoids J}
    (e : X.toGroupoids ≅ Y.toGroupoids) :
    Hom.lift e.hom ≫ Hom.lift e.inv = 𝟙 X := sorry

/-- Lifting the two directions of a groupoid-fibred isomorphism satisfies the second inverse
law. -/
@[stacks 02ZK "inverse forward law for lifted groupoid-stack isomorphisms"]
theorem inv_comp_hom {X Y : StackOver.Groupoids J}
    (e : X.toGroupoids ≅ Y.toGroupoids) :
    Hom.lift e.inv ≫ Hom.lift e.hom = 𝟙 Y := sorry

end isoOfGroupoids

/-- Lift an isomorphism of the underlying groupoid-fibred categories to an isomorphism of
stacks in groupoids. -/
@[stacks 02ZK "groupoid-stack isomorphism lifting constructor"]
def isoOfGroupoids {X Y : StackOver.Groupoids J}
    (e : X.toGroupoids ≅ Y.toGroupoids) : X ≅ Y where
  hom := Hom.lift e.hom
  inv := Hom.lift e.inv
  hom_inv_id := isoOfGroupoids.hom_comp_inv e
  inv_hom_id := isoOfGroupoids.inv_comp_hom e

namespace isoOfGroupoids

/-- The groupoid-fibred projection of the forward map of `isoOfGroupoids` is the supplied
forward map. -/
@[simp, stacks 02ZK "forward projection of lifted groupoid-stack isomorphism"]
theorem hom.toGroupoidsMor {X Y : StackOver.Groupoids J}
    (e : X.toGroupoids ≅ Y.toGroupoids) :
    Hom.toGroupoidsMor (isoOfGroupoids e).hom = e.hom := sorry

/-- The groupoid-fibred projection of the inverse map of `isoOfGroupoids` is the supplied
inverse map. -/
@[simp, stacks 02ZK "inverse projection of lifted groupoid-stack isomorphism"]
theorem inv.toGroupoidsMor {X Y : StackOver.Groupoids J}
    (e : X.toGroupoids ≅ Y.toGroupoids) :
    Hom.toGroupoidsMor (isoOfGroupoids e).inv = e.inv := sorry

end isoOfGroupoids

end StackOver.Groupoids

end CategoryTheory
