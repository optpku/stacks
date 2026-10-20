module

public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Acyclic

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Definition 111.30.7: a cochain complex of finite filtered objects is filtered acyclic when
each integer graded-piece complex is acyclic. -/
#check (CategoryTheory.FilteredObject.Finite.CochainComplex.acyclic :
  CochainComplex (CategoryTheory.FilteredObject.Finite.category C) ℤ → Prop)
