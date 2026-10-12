/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.FiniteForget
public import ReasLib.CategoryTheory.Filtration.FiniteBiproduct
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated structure on finite filtered homotopy complexes

Finite filtered objects inherit the canonical biproducts of filtered objects.  This leaf records
the resulting pretriangulated and triangulated structures on their homotopy category, without
mentioning derived localizations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace Finite.Homotopy

/-- The homotopy category of finite filtered cochain complexes is pretriangulated. -/
@[stacks 05S1 "finite filtered homotopy category"]
noncomputable instance pretriangulated :
    Pretriangulated (HomotopyCategory (FilteredObject.Finite.category C) (up ℤ)) :=
  inferInstance

/-- The homotopy category of finite filtered cochain complexes is triangulated. -/
@[stacks 05S1 "finite filtered homotopy category"]
noncomputable instance isTriangulated :
    IsTriangulated (HomotopyCategory (FilteredObject.Finite.category C) (up ℤ)) :=
  inferInstance

end Finite.Homotopy

namespace Finite.AssociatedGraded.Homotopy

/-- The finite associated-graded homotopy functor is triangulated. -/
@[stacks 05S1 "finite filtered associated-graded homotopy functor"]
noncomputable instance isTriangulated :
    (Finite.AssociatedGraded.homotopy C).IsTriangulated := sorry

end Finite.AssociatedGraded.Homotopy

namespace Finite.Forget.Homotopy

/-- The finite filtered forgetful homotopy functor is triangulated. -/
@[stacks 05S1 "finite filtered forgetful homotopy functor"]
noncomputable instance isTriangulated :
    (Finite.Forget.homotopy C).IsTriangulated := sorry

end Finite.Forget.Homotopy

end CategoryTheory.FilteredObject
