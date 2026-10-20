module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-morphisms of bundled stacks

This file owns the ambient and based-natural-transformation views of `2`-morphisms between
morphisms of bundled stacks.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

namespace StackOver.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.{u, v, w, vS} J}

/-- Lift a `2`-morphism between ambient morphisms to a `2`-morphism between stack morphisms. -/
@[stacks 02ZG "lift an ambient stack 2-morphism"]
abbrev lift₂ {F G : X ⟶ Y} (eta : toMor F ⟶ toMor G) : F ⟶ G :=
  Bicategory.InducedBicategory.Hom₂.mk eta

/-- The underlying `2`-morphism between ambient morphisms. -/
@[stacks 02ZG "underlying 2-morphism of stack morphisms"]
abbrev toMor₂ {F G : X ⟶ Y} (eta : F ⟶ G) : toMor F ⟶ toMor G := eta.hom

end StackOver.Hom

namespace StackOver.Hom₂

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.{u, v, w, vS} J}
variable {F G : X ⟶ Y}

/-- The based natural transformation underlying a `2`-morphism of stack morphisms. -/
@[stacks 02ZG "based natural transformation of a stack 2-morphism"]
abbrev toBasedNatTrans (eta : F ⟶ G) :
    StackOver.Hom.toBasedFunctor F ⟶ StackOver.Hom.toBasedFunctor G :=
  (StackOver.Hom.toMor₂ eta).hom

/-- The ordinary natural transformation on total categories underlying a `2`-morphism of
stack morphisms. -/
@[stacks 02ZG "total natural transformation of a stack 2-morphism"]
abbrev toNatTrans (eta : F ⟶ G) :
    StackOver.Hom.toFunctor F ⟶ StackOver.Hom.toFunctor G :=
  (toBasedNatTrans eta).toNatTrans

/-- Build a `2`-morphism of stack morphisms from a based natural transformation. -/
@[stacks 02ZG "construct a stack 2-morphism from a based transformation"]
def ofBasedNatTrans
    (eta : StackOver.Hom.toBasedFunctor F ⟶ StackOver.Hom.toBasedFunctor G) :
    F ⟶ G :=
  StackOver.Hom.lift₂ (ObjectProperty.homMk eta)

namespace ofBasedNatTrans

/-- Projecting a `2`-morphism built by `ofBasedNatTrans` recovers the supplied based natural
transformation. -/
@[stacks 02ZG "based transformation constructor round trip", simp]
theorem toBasedNatTrans
    (eta : StackOver.Hom.toBasedFunctor F ⟶ StackOver.Hom.toBasedFunctor G) :
    StackOver.Hom₂.toBasedNatTrans (ofBasedNatTrans eta) = eta := sorry

/-- The total natural transformation underlying `ofBasedNatTrans eta` is the total natural
transformation of `eta`. -/
@[stacks 02ZG "total transformation constructor round trip", simp]
theorem toNatTrans
    (eta : StackOver.Hom.toBasedFunctor F ⟶ StackOver.Hom.toBasedFunctor G) :
    StackOver.Hom₂.toNatTrans (ofBasedNatTrans eta) = eta.toNatTrans := sorry

end ofBasedNatTrans

end StackOver.Hom₂

end CategoryTheory
