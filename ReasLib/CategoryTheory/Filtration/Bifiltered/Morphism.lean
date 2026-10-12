/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Bifiltered.Object
public import ReasLib.CategoryTheory.Filtration.Morphism

@[expose] public section

/-!
# Morphisms of bifiltered objects

A morphism of bifiltered objects is one underlying morphism preserving both filtrations.
-/

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.BifilteredObject

variable {C : Type u} [Category.{v} C]

/-- A morphism preserving both filtrations of two bifiltered objects. -/
@[ext]
structure Hom (X Y : BifilteredObject C) where
  /-- The common underlying morphism. -/
  hom : X.obj ⟶ Y.obj
  /-- The underlying morphism preserves the first filtration. -/
  preservesFirst (i : ℤ) :
    (Y.firstFiltration.stage i).Factors ((X.firstFiltration.stage i).arrow ≫ hom)
  /-- The underlying morphism preserves the second filtration. -/
  preservesSecond (i : ℤ) :
    (Y.secondFiltration.stage i).Factors ((X.secondFiltration.stage i).arrow ≫ hom)

namespace Hom

variable {X Y Z : BifilteredObject C}

/-- Retain the first-filtration component of a bifiltered morphism. -/
def first (f : Hom X Y) : FilteredObject.Hom X.firstObj Y.firstObj where
  hom := f.hom
  preserves := f.preservesFirst

/-- Retain the second-filtration component of a bifiltered morphism. -/
def second (f : Hom X Y) : FilteredObject.Hom X.secondObj Y.secondObj where
  hom := f.hom
  preserves := f.preservesSecond

/-- Exchange the two filtration-preservation conditions of a bifiltered morphism. -/
def swap (f : Hom X Y) : Hom X.swapObj Y.swapObj where
  hom := f.hom
  preservesFirst := f.preservesSecond
  preservesSecond := f.preservesFirst

/-- The identity morphism of a bifiltered object. -/
def id (X : BifilteredObject C) : Hom X X where
  hom := 𝟙 X.obj
  preservesFirst := (FilteredObject.Hom.id X.firstObj).preserves
  preservesSecond := (FilteredObject.Hom.id X.secondObj).preserves

/-- Composition of morphisms preserving both filtrations. -/
def comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  hom := f.hom ≫ g.hom
  preservesFirst := (FilteredObject.Hom.comp f.first g.first).preserves
  preservesSecond := (FilteredObject.Hom.comp f.second g.second).preserves

end Hom

end CategoryTheory.BifilteredObject
