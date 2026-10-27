/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic.Existence
public import ReasLib.RingTheory.Completion.LocalRing
public import Mathlib.RingTheory.DedekindDomain.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- Every field admits an intrinsic dualizing complex for canonical module `RHom`.
The historical namespace is retained; no ambient closed structure is selected. -/
theorem exists_of_field
    (k : Type u) [Field k] :
    ∃ ω : DerivedCategory (ModuleCat.{u} k),
      CategoryTheory.DerivedCategory.IsDualizing ω := sorry

/-- Every Noetherian complete local commutative ring admits an intrinsic dualizing complex
for canonical module `RHom`. -/
theorem exists_of_completeLocal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] :
    ∃ ω : DerivedCategory (ModuleCat.{u} A),
      CategoryTheory.DerivedCategory.IsDualizing ω :=
  CategoryTheory.DerivedCategory.IsDualizing.exists_of_completeLocal A

/-- The ring of integers admits an intrinsic dualizing complex for canonical module `RHom`. -/
theorem exists_int :
    ∃ ω : DerivedCategory (ModuleCat.{0} ℤ),
      CategoryTheory.DerivedCategory.IsDualizing ω := sorry

/-- Every Dedekind domain admits an intrinsic dualizing complex for canonical module `RHom`. -/
theorem exists_of_dedekindDomain
    (A : Type u) [CommRing A] [IsDedekindDomain A] :
    ∃ ω : DerivedCategory (ModuleCat.{u} A),
      CategoryTheory.DerivedCategory.IsDualizing ω := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
