/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.CommSq

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsProper

/-- If a composite is universally closed and its first factor is surjective, then its
separated, locally finite type second factor is proper. -/
theorem of_comp_surjective {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] (hfg : UniversallyClosed (f ≫ g)) [IsSeparated g]
    [LocallyOfFiniteType g] : IsProper g := sorry

/-- In a commutative square whose left map is surjective and whose top and right maps are
proper, a separated, locally finite type bottom map is proper. -/
theorem of_surjective_commSq {S X P X' : Scheme.{u}} {f : X ⟶ S} {p : P ⟶ S}
    (toP : X' ⟶ P) (π : X' ⟶ X) (hcomm : CommSq toP π p f)
    [Surjective π] [IsProper toP] [IsProper p] [IsSeparated f]
    [LocallyOfFiniteType f] : IsProper f := sorry

end AlgebraicGeometry.IsProper
