module

public import ReasLib.CategoryTheory.Filtration.Complex.Finite

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.FilteredObject.Finite.CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A cochain complex of finite filtered objects is filtered acyclic when its associated-graded
complex is acyclic. -/
abbrev acyclic (K : CochainComplex (FilteredObject.Finite.category C) ℤ) : Prop :=
  ((AssociatedGraded.cochain C).obj K).Acyclic

/-- Filtered acyclicity of a complex of `Filᶠ(C)` is equivalent to acyclicity of each graded-piece
complex `gr^p(K)`. -/
theorem acyclic_iff (K : CochainComplex (FilteredObject.Finite.category C) ℤ) :
    acyclic K ↔
      ∀ p : ℤ,
        (((AssociatedGraded.functor C ⋙ GradedObject.eval p).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).Acyclic :=
  sorry

/-- Filtered acyclicity implies acyclicity of every associated-graded piece complex. -/
theorem gradedPiece_acyclic (K : CochainComplex (FilteredObject.Finite.category C) ℤ)
    (hK : acyclic K) (p : ℤ) :
    (((AssociatedGraded.functor C ⋙ GradedObject.eval p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).Acyclic :=
  sorry

/-- Filtered acyclicity of a cochain complex of `Filᶠ(C)` is equivalent to membership of its
homotopy class in `Homotopy.acyclic`. -/
theorem acyclic_iff_homotopy (K : CochainComplex (FilteredObject.Finite.category C) ℤ) :
    acyclic K ↔
      Homotopy.acyclic C
        ((HomotopyCategory.quotient (FilteredObject.Finite.category C)
            (ComplexShape.up ℤ)).obj K) :=
  sorry

end CategoryTheory.FilteredObject.Finite.CochainComplex
