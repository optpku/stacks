module

import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Lifting
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Exercise 111.30.11 (1): homotopy lifting of a cochain map into a bounded-below complex of
filtered injectives along a filtered quasi-isomorphism. -/
@[stacks 028I]
#check (CochainComplex.FilteredInjectivePlus.exists_homotopy_lift :
  ∀ (I : CochainComplex.FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ (CochainComplex.FilteredInjectivePlus.ι C).obj I),
    ∃ β : L ⟶ (CochainComplex.FilteredInjectivePlus.ι C).obj I,
      Nonempty (Homotopy (α ≫ β) γ))

/- Exercise 111.30.11 (2): strict commuting lift when the filtered quasi-isomorphism is a
strict monomorphism in every degree. -/
@[stacks 028I]
#check (CochainComplex.FilteredInjectivePlus.exists_lift_of_termwiseStrictMono :
  ∀ (I : CochainComplex.FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ (CochainComplex.FilteredInjectivePlus.ι C).obj I)
    (hmono : ∀ n : ℤ, Mono (α.f n))
    (hstrict : ∀ n : ℤ,
      FilteredObject.Hom.Strict ((FilteredObject.Finite.inclusion C).map (α.f n))),
    ∃ β : L ⟶ (CochainComplex.FilteredInjectivePlus.ι C).obj I, α ≫ β = γ)
