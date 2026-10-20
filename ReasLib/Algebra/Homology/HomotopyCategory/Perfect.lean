/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect homotopy category

The homotopy category `K_perf(R)` of bounded complexes of finite projective left `R`-modules,
together with the fully faithful functor into `D(R)` whose essential image is the perfect objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ComplexShape

universe u

namespace HomotopyCategory

variable (R : Type u) [Ring R]

/-- Homotopy-category objects whose underlying cochain complex is bounded and termwise finite
projective. -/
@[stacks 03TH]
protected def perfect : ObjectProperty (HomotopyCategory (ModuleCat.{u} R) (up ℤ)) :=
  fun K ↦ CochainComplex.IsBoundedFiniteProjective K.as

/-- A homotopy-category object is perfect exactly when its underlying complex is bounded
finite projective. -/
lemma perfect_iff (K : HomotopyCategory (ModuleCat.{u} R) (up ℤ)) :
    HomotopyCategory.perfect R K ↔ CochainComplex.IsBoundedFiniteProjective K.as := sorry

/-- The homotopy category of bounded complexes of finite projective left `R`-modules. -/
@[stacks 03TH]
abbrev Perfect := (HomotopyCategory.perfect R).FullSubcategory

namespace Perfect

/-- The inclusion of the perfect homotopy category into the ambient homotopy category. -/
abbrev ι : Perfect R ⥤ HomotopyCategory (ModuleCat.{u} R) (up ℤ) :=
  (HomotopyCategory.perfect R).ι

/-- The homotopy class of a bounded finite-projective cochain complex, as an object of the
perfect homotopy category. -/
def ofComplex (L : CochainComplex (ModuleCat.{u} R) ℤ)
    [hL : CochainComplex.IsBoundedFiniteProjective L] : Perfect R :=
  ⟨(HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)).obj L, hL⟩

/-- The underlying cochain complex of `ofComplex L` is `L`. -/
theorem ofComplex_as (L : CochainComplex (ModuleCat.{u} R) ℤ)
    [CochainComplex.IsBoundedFiniteProjective L] :
    (ofComplex R L).obj.as = L := sorry

/-- The canonical functor from the perfect homotopy category to the derived category. -/
@[stacks 03TH]
def toDerived : Perfect R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  ι R ⋙ DerivedCategory.Qh

/-- The functor from the perfect homotopy category to the derived category is full. -/
@[stacks 03TH]
instance instFullToDerived : (toDerived R).Full := sorry

/-- The functor from the perfect homotopy category to the derived category is faithful. -/
@[stacks 03TH]
instance instFaithfulToDerived : (toDerived R).Faithful := sorry

/-- Hom-sets in the perfect homotopy category map bijectively to Hom-sets in the derived
category. -/
theorem toDerived_map_bijective {P Q : Perfect R} :
    Function.Bijective
      ((toDerived R).map : (P ⟶ Q) → ((toDerived R).obj P ⟶ (toDerived R).obj Q)) := sorry

/-- The essential image of the perfect homotopy category in `D(R)` is the class of perfect
objects. -/
@[stacks 03TH]
theorem mem_essImage_toDerived_iff (K : DerivedCategory (ModuleCat.{u} R)) :
    (toDerived R).essImage K ↔ K.IsPerfect := sorry

end Perfect

end HomotopyCategory
