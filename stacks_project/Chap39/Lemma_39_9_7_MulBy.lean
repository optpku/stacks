/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.MulBy

@[expose] public section

open CategoryTheory
open scoped AbelianVariety CategoryTheory.MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable (G : C) [GrpObj G] (n : ℕ)

#check (CategoryTheory.GrpObj.mulBy G n : G ⟶ G)

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable (A : SchemeOverField k) [GrpObj A] (m : ℕ)

#check (SchemeOverField.mulBy A m : A.left ⟶ A.left)

#check ([m]ₐ A : A.left ⟶ A.left)

end AlgebraicGeometry
