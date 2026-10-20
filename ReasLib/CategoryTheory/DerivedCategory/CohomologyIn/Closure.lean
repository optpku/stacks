/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure
public import ReasLib.CategoryTheory.ObjectProperty.Retract.InverseImage
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Closure Properties of Cohomology-In Subcategories

This leaf contains the closure results that need more than the elementary degreewise membership
API: retract stability and the weak-Serre triangulated structure.  Colimit closure is isolated in
`CohomologyIn.Colimits`.
-/

noncomputable section

universe w u v

open CategoryTheory

namespace CategoryTheory

open Limits ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

namespace DerivedCategory.CohomologyIn

/-- Retract stability of the coefficient property implies retract stability of the associated
cohomology-in property. -/
@[stacks 06UQ "retract-stable cohomology-in construction"]
instance stableUnderRetractsOf (P : ObjectProperty A)
    [P.IsStableUnderRetracts] :
    (DerivedCategory.cohomologyIn P).IsStableUnderRetracts := sorry

/-- The cohomology-in property of a weak Serre class is triangulated. -/
@[stacks 06UQ "triangulated weak-Serre cohomology-in subcategory"]
instance triangulated (P : ObjectProperty A) [IsWeakSerreClass P] :
    (DerivedCategory.cohomologyIn P).IsTriangulated := sorry

end DerivedCategory.CohomologyIn

end CategoryTheory
