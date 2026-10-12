/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.RingTheory.Completion.LocalRing
public import Mathlib.RingTheory.DedekindDomain.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- Every field admits a dualizing complex in its derived category of modules. -/
theorem exists_of_field
    (k : Type u) [Field k]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} k))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} k))) :
    ∃ ω : DerivedCategory (ModuleCat.{u} k), ω.IsDualizingComplex H := sorry

/-- Every Noetherian complete local commutative ring admits a dualizing complex. -/
theorem exists_of_completeLocal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) :
    ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H := sorry

/-- The ring of integers admits a dualizing complex in its derived category of modules. -/
theorem exists_int
    [MonoidalCategory (DerivedCategory (ModuleCat.{0} ℤ))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{0} ℤ))) :
    ∃ ω : DerivedCategory (ModuleCat.{0} ℤ), ω.IsDualizingComplex H := sorry

/-- Every Dedekind domain admits a dualizing complex. -/
theorem exists_of_dedekindDomain
    (A : Type u) [CommRing A] [IsDedekindDomain A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) :
    ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
