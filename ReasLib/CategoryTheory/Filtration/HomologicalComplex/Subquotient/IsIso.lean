/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Subquotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism transport for filtered homological-complex subquotients

The subquotient functor transports isomorphisms.  Both the bundled map and each degree component
are exposed as instances for direct downstream use.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.HomologicalComplex.Filtered.Subquotient

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}
variable {K L : HomologicalComplex (FilteredObject C) c}

/-- Every degree component of a subquotient map is an isomorphism when the source map is. -/
@[stacks 0BKI "isomorphism on filtered subquotient components"]
noncomputable instance map_f_isIso (f : K ⟶ L) (i : ι) {p q : ℤ} (hpq : p ≤ q)
    [IsIso f] : IsIso ((map f hpq).f i) := sorry

/-- A filtered subquotient map is an isomorphism when its source map is. -/
@[stacks 0BKI "isomorphism of filtered subquotient maps"]
noncomputable instance map_isIso (f : K ⟶ L) {p q : ℤ} (hpq : p ≤ q)
    [IsIso f] : IsIso (map f hpq) := sorry

end CategoryTheory.HomologicalComplex.Filtered.Subquotient
