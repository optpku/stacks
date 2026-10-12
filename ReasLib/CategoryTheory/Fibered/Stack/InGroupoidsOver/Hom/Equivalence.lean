/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Computations

/-!
# Hom equivalence for stacks in groupoids

This file packages the canonical equivalence and forgetful functor between stack morphisms and
their ambient groupoid-fibred morphisms.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Groupoids.Hom

variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Groupoids J}

/-- The canonical equivalence from the ambient groupoid-fibred Hom category to the Hom category
of stacks in groupoids. -/
@[stacks 02ZK "groupoid-stack ambient Hom category equivalence"]
abbrev ambientEquivalence :
    (X.toGroupoids ⟶ Y.toGroupoids) ≌ (X ⟶ Y) :=
  Bicategory.InducedBicategory.homEquivalence X Y

/-- The forgetful functor from stack morphisms to ambient groupoid-fibred morphisms. -/
@[stacks 02ZK "groupoid-stack ambient Hom forgetful functor"]
abbrev ambientFunctor :
    (X ⟶ Y) ⥤ (X.toGroupoids ⟶ Y.toGroupoids) :=
  ambientEquivalence.inverse

/-- Lift an isomorphism of ambient groupoid-fibred morphisms to the induced Hom category of
stacks in groupoids. -/
@[stacks 02ZK "groupoid-stack ambient Hom isomorphism lift"]
noncomputable def isoMk {F G : X ⟶ Y}
    (e : toGroupoidsMor F ≅ toGroupoidsMor G) : F ≅ G :=
  Bicategory.InducedBicategory.isoMk e

end StackOver.Groupoids.Hom

end CategoryTheory
