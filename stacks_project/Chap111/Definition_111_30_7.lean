module

public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Acyclic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Definition 111.30.7: in an abelian category `𝒜`, a cochain complex `K` of `Filᶠ(𝒜)` is
filtered acyclic when for every `p : ℤ` the graded-piece complex `gr^p(K)` is acyclic. The
reusable cochain-level owner is `FilteredObject.Finite.CochainComplex.acyclic`. -/
@[stacks 028E] #check (CategoryTheory.FilteredObject.Finite.CochainComplex.acyclic :
  CochainComplex (CategoryTheory.FilteredObject.Finite.category C) ℤ → Prop)
