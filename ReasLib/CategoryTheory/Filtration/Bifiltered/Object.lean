module

public import ReasLib.CategoryTheory.Filtration.Object

@[expose] public section

/-!
# Bifiltered objects

A bifiltered object carries two decreasing filtrations by subobjects of one common underlying
object. This strict common-object model is the neutral owner for bifiltered complexes.
-/

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- An object equipped with two decreasing `ℤ`-indexed filtrations on the same underlying
object. -/
@[stacks 0ESK "bifiltered object"]
structure BifilteredObject where
  /-- The common underlying object. -/
  obj : C
  /-- The first decreasing filtration. -/
  firstFiltration : DecreasingFiltration obj
  /-- The second decreasing filtration. -/
  secondFiltration : DecreasingFiltration obj

namespace BifilteredObject

variable {C}

/-- The filtered object obtained by retaining the first filtration. -/
def firstObj (X : BifilteredObject C) : FilteredObject C where
  obj := X.obj
  filtration := X.firstFiltration

/-- The filtered object obtained by retaining the second filtration. -/
def secondObj (X : BifilteredObject C) : FilteredObject C where
  obj := X.obj
  filtration := X.secondFiltration

/-- Exchange the two filtrations of a bifiltered object. -/
def swapObj (X : BifilteredObject C) : BifilteredObject C where
  obj := X.obj
  firstFiltration := X.secondFiltration
  secondFiltration := X.firstFiltration

end BifilteredObject

end CategoryTheory
