module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Value
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# Cohomology of Bounded-Below Right Derived Values

This leaf specializes `Functor.RightDerived.Bounded.valueFunctor` to a functor induced by an
additive functor between abelian categories, then takes a cohomology object in the target derived
category.  The functorial owner is exposed before the object and arrow abbreviations, so filtered
and spectral-sequence applications can use ordinary `Functor` APIs without rebuilding maps.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- The degree-`n` cohomology functor of the total bounded-below right-derived value of `F`,
computed using the localization model `Q`. -/
@[stacks 015H "bounded-below total right-derived cohomology functor"]
noncomputable abbrev cohomologyFunctor
    (F : A ⥤ B) [F.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℤ) : CochainComplex.Plus A ⥤ B :=
  valueFunctor F.toBoundedBelowDerived Q ⋙
    DerivedCategory.Plus.homologyFunctor B n

namespace cohomologyFunctor

/-- Object computation for the bounded-below right-derived cohomology functor. -/
@[simp, stacks 015H "bounded-below total right-derived cohomology object computation"]
theorem obj
    (F : A ⥤ B) [F.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℤ) (K : CochainComplex.Plus A) :
    (cohomologyFunctor F Q n).obj K =
      (DerivedCategory.Plus.homologyFunctor B n).obj
        ((valueFunctor F.toBoundedBelowDerived Q).obj K) := sorry

/-- Morphism computation for the bounded-below right-derived cohomology functor. -/
@[simp, stacks 015H "bounded-below total right-derived cohomology map computation"]
theorem map
    (F : A ⥤ B) [F.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℤ) {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (cohomologyFunctor F Q n).map f =
      (DerivedCategory.Plus.homologyFunctor B n).map
        ((valueFunctor F.toBoundedBelowDerived Q).map f) := sorry

end cohomologyFunctor

/-- The degree-`n` cohomology object of the total bounded-below right-derived value of `F` at
`K`, computed using the localization model `Q`. -/
@[stacks 015H "bounded-below total right-derived cohomology"]
noncomputable abbrev cohomology
    (F : A ⥤ B) [F.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) (n : ℤ) : B :=
  (cohomologyFunctor F Q n).obj K

/-- The map on bounded-below right-derived cohomology induced by a cochain map. -/
@[stacks 015H "bounded-below total right-derived cohomology map"]
noncomputable abbrev cohomologyMap
    (F : A ⥤ B) [F.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {K L : CochainComplex.Plus A} (f : K ⟶ L) (n : ℤ) :
    cohomology F Q K n ⟶ cohomology F Q L n :=
  (cohomologyFunctor F Q n).map f

/-- Evaluation of the cohomology functor is the source-facing cohomology abbreviation. -/
@[simp, stacks 015H "bounded-below total right-derived cohomology object computation"]
theorem cohomologyFunctor_obj
    (F : A ⥤ B) [F.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℤ) (K : CochainComplex.Plus A) :
    (cohomologyFunctor F Q n).obj K = cohomology F Q K n := sorry

/-- The map of the cohomology functor is the source-facing cohomology map. -/
@[simp, stacks 015H "bounded-below total right-derived cohomology map computation"]
theorem cohomologyFunctor_map
    (F : A ⥤ B) [F.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℤ) {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (cohomologyFunctor F Q n).map f = cohomologyMap F Q f n := sorry

/-- The cohomology map of an identity cochain map is an identity. -/
@[simp, stacks 015H "bounded-below total right-derived cohomology map identity"]
theorem cohomologyMap_id
    (F : A ⥤ B) [F.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) (n : ℤ) :
    cohomologyMap F Q (𝟙 K) n = 𝟙 (cohomology F Q K n) := sorry

/-- Cohomology maps preserve composition of cochain maps. -/
@[reassoc, stacks 015H "bounded-below total right-derived cohomology map composition"]
theorem cohomologyMap_comp
    (F : A ⥤ B) [F.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {K L M : CochainComplex.Plus A} (f : K ⟶ L) (g : L ⟶ M) (n : ℤ) :
    cohomologyMap F Q (f ≫ g) n =
      cohomologyMap F Q f n ≫ cohomologyMap F Q g n := sorry

end CategoryTheory.Functor.RightDerived.Bounded
