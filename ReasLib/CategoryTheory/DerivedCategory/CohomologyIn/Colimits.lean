/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits of Cohomology-In Objects

This leaf isolates the colimit assumptions from the finite-limit and triangulated structure of
cohomology-in subcategories.
-/

@[expose] public section

noncomputable section

universe w u v

open CategoryTheory

namespace CategoryTheory

open Limits ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

namespace DerivedCategory.CohomologyIn

/-- The cohomology-in property is closed under `J`-indexed colimits when `P` is and every
cohomology functor preserves such colimits. -/
instance closedUnderColimits (P : ObjectProperty A) {J : Type*} [Category J]
    [P.IsClosedUnderColimitsOfShape J]
    [∀ n : ℤ, PreservesColimitsOfShape J (DerivedCategory.homologyFunctor A n)] :
    (DerivedCategory.cohomologyIn P).IsClosedUnderColimitsOfShape J := sorry

end DerivedCategory.CohomologyIn

end CategoryTheory
