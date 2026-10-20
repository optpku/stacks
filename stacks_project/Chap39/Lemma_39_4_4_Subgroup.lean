/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup.Factorization

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Over

variable {S : AlgebraicGeometry.Scheme.{u}} {H G : Over S}

/-- A morphism in `Over S` is monic when its underlying scheme map is a closed immersion. -/
theorem mono_of_isClosedImmersion_left (j : H ⟶ G)
    [AlgebraicGeometry.IsClosedImmersion j.left] : Mono j :=
  Over.mono_of_mono_left j

end CategoryTheory.Over

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {H G : C} [GrpObj G] (j : H ⟶ G) [Mono j]

#check (Factorization.equivRestriction j : Factorization j ≃ Restriction j)

end CategoryTheory.GrpObj
