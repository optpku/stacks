module

import ReasLib.CategoryTheory.Filtration.Complex.InjectiveResolution
import StacksCheckRecall

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.FiniteFilteredDiagram

/- Exercise 111.30.10: a bounded-below complex of finite filtered objects over an abelian
category with enough injectives admits a filtered quasi-isomorphism to a bounded-below
complex of filtered-injective objects. In fact the comparison may be chosen termwise as a
strict monomorphism. -/

@[stacks 028H] #check (CategoryTheory.FiniteFilteredDiagram.exists_strictInjectiveResolution :
  ∀ {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (a : ℤ) (K : CochainComplex (category C) ℤ), K.IsStrictlyGE a →
    ∃ (I : CochainComplex (category C) ℤ) (α : K ⟶ I),
      I.IsStrictlyGE a ∧
      (∀ n : ℤ, IsFilteredInjective (I.X n)) ∧
      (∀ p : ℤ, QuasiIso
        (((gradedPieceFunctor (C := C) p).mapHomologicalComplex (ComplexShape.up ℤ)).map α)) ∧
      ∀ n : ℤ, IsStrictMono (α.f n))

end
