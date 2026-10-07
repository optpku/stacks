module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import ReasLib.CategoryTheory.Filtration.FinitePreadditive
public import ReasLib.CategoryTheory.Filtration.Strict
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting into bounded-below filtered-injective cochain complexes

This is the filtered analogue of `CochainComplex.InjectivePlus` lifting. It exposes homotopy
and strict cochain lifts into a `FilteredInjectivePlus` target along a filtered
quasi-isomorphism of complexes of finite filtered objects.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredInjectivePlus

/-- A cochain map into a bounded-below complex of filtered injectives lifts along a filtered
quasi-isomorphism up to homotopy. -/
@[stacks 028I]
theorem exists_homotopy_lift (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ (FilteredInjectivePlus.ι C).obj I) :
    ∃ β : L ⟶ (FilteredInjectivePlus.ι C).obj I, Nonempty (Homotopy (α ≫ β) γ) := sorry

/-- If the filtered quasi-isomorphism is a strict monomorphism in every degree, a map into a
bounded-below complex of filtered injectives admits a strictly commuting lift. -/
@[stacks 028I]
theorem exists_lift_of_termwiseStrictMono (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ (FilteredInjectivePlus.ι C).obj I)
    (hmono : ∀ n : ℤ, Mono (α.f n))
    (hstrict : ∀ n : ℤ,
      FilteredObject.Hom.Strict ((FilteredObject.Finite.inclusion C).map (α.f n))) :
    ∃ β : L ⟶ (FilteredInjectivePlus.ι C).obj I, α ≫ β = γ := sorry

end FilteredInjectivePlus

end CochainComplex
