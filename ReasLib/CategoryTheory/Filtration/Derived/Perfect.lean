/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.Algebra.Homology.HomotopyCategory.FilteredPerfect
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.CategoryTheory.Filtration.Derived.AssociatedGraded
public import ReasLib.CategoryTheory.Filtration.Derived.Forget

/-!
# Perfect objects in the finite filtered derived category

Filtered-perfect derived objects have bounded filtered finite-projective
representatives. Their underlying and associated-graded derived objects are perfect.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ComplexShape
open scoped FilteredObject.Finite ZeroObject

universe u

namespace CategoryTheory.FilteredObject.FiniteDerived.Quotient

variable {Λ : Type u} [Ring Λ]
variable [CategoryWithHomology (GradedObject ℤ (ModuleCat.{u} Λ))]

/-- The image of a cochain complex of finite filtered modules in `DF(ModuleCat Λ)`. -/
noncomputable abbrev ofCochainComplex
    (L : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ) :
    Category (ModuleCat.{u} Λ) :=
  (functor (ModuleCat.{u} Λ)).obj
    ((HomotopyCategory.quotient (Filᶠ(ModuleCat.{u} Λ)) (up ℤ)).obj L)

end CategoryTheory.FilteredObject.FiniteDerived.Quotient

namespace CategoryTheory.FilteredObject.FiniteDerived

variable {Λ : Type u} [Ring Λ]
variable [CategoryWithHomology (GradedObject ℤ (ModuleCat.{u} Λ))]

/-- An object of `DF(ModuleCat Λ)` is perfect if it is isomorphic to the image of a
bounded cochain complex of filtered finite projective objects of `Filᶠ(ModuleCat Λ)`. -/
def IsPerfect (K : Quotient.Category (ModuleCat.{u} Λ)) : Prop :=
  ∃ (L : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ)
    (_ : K ≅ Quotient.ofCochainComplex L),
    CochainComplex.IsBoundedFilteredFiniteProjective L

namespace IsPerfect

/-- Perfectness in the finite filtered derived category is invariant under
isomorphism. -/
theorem of_iso {K L : Quotient.Category (ModuleCat.{u} Λ)} (e : K ≅ L)
    (hL : IsPerfect L) : IsPerfect K :=
  sorry

variable [HasDerivedCategory (GradedObject ℤ (ModuleCat.{u} Λ))]

/-- Forgetting the filtration of a filtered-perfect derived object yields a perfect
object of `D(ModuleCat Λ)`. -/
theorem forget {K : Quotient.Category (ModuleCat.{u} Λ)} (hK : IsPerfect K) :
    DerivedCategory.IsPerfect ((Forget.canonicalLift (ModuleCat.{u} Λ)).obj K) :=
  sorry

/-- Each associated-graded piece of a filtered-perfect derived object is a perfect
object of `D(ModuleCat Λ)`. -/
theorem gradedPiece {K : Quotient.Category (ModuleCat.{u} Λ)} (hK : IsPerfect K)
    (p : ℤ) :
    DerivedCategory.IsPerfect ((GradedPiece.canonicalLift (ModuleCat.{u} Λ) p).obj K) :=
  sorry

end IsPerfect

end CategoryTheory.FilteredObject.FiniteDerived

namespace CategoryTheory.HomotopyCategory.FilteredPerfect

variable {Λ : Type u} [Ring Λ]
variable [CategoryWithHomology (GradedObject ℤ (ModuleCat.{u} Λ))]

/-- The essential image of the filtered-perfect homotopy category in `DF(ModuleCat Λ)`
is the class of filtered-perfect derived objects. -/
theorem mem_essImage_toDerived_iff
    (K : FilteredObject.FiniteDerived.Quotient.Category (ModuleCat.{u} Λ)) :
    (toDerived Λ).essImage K ↔ FilteredObject.FiniteDerived.IsPerfect K :=
  sorry

end CategoryTheory.HomotopyCategory.FilteredPerfect
