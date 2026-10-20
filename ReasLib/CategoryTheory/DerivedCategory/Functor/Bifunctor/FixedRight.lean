module

public import ReasLib.Algebra.Homology.HomotopyCategory.TotalFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-! # Fixed-right derived additive bifunctors -/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v u w

namespace CategoryTheory.DerivedCategory.Bifunctor.Right

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasDerivedCategory.{w} C]
variable (T : C ⥤ C ⥤ C) [T.Additive] [∀ X : C, (T.obj X).Additive]
variable [∀ (K L : CochainComplex C ℤ),
  HomologicalComplex.HasMapBifunctor K L T (up ℤ)]

/-- Fixed-right totalization on the homotopy category followed by derived localization,
using a complex representative of the fixed derived object. -/
abbrev sourceFunctor (E : DerivedCategory C) :
    HomotopyCategory C (up ℤ) ⥤ DerivedCategory C :=
  Functor.Homotopy.BifunctorTotal.rightFixed T
    ((DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objPreimage E) ⋙
      (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)

variable (E : DerivedCategory C)
variable [(sourceFunctor T E).HasLeftDerivedFunctor (HomotopyCategory.quasiIso C (up ℤ))]

/-- The total left derived functor of totalization with a fixed right derived object. -/
abbrev functor : DerivedCategory C ⥤ DerivedCategory C :=
  (sourceFunctor T E).totalLeftDerived
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C (up ℤ))

/-- The value of the derived bifunctor at a variable left object and a fixed right object. -/
abbrev obj (K E : DerivedCategory C)
    [(sourceFunctor T E).HasLeftDerivedFunctor (HomotopyCategory.quasiIso C (up ℤ))] :
    DerivedCategory C :=
  (functor T E).obj K

/-- The canonical comparison from the derived fixed-right functor to its homotopy source. -/
abbrev counit :
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C) ⋙
      functor T E ⟶ sourceFunctor T E :=
  (sourceFunctor T E).totalLeftDerivedCounit
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C (up ℤ))

/-- The fixed-right derived functor and its comparison satisfy the left-derived universal
property with respect to quasi-isomorphisms. -/
instance isLeftDerived :
    (functor T E).IsLeftDerivedFunctor (counit T E)
      (HomotopyCategory.quasiIso C (up ℤ)) := by
  infer_instance

end CategoryTheory.DerivedCategory.Bifunctor.Right

end
