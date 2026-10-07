module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Subquotient
public import ReasLib.CategoryTheory.Filtration.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation for filtered homological-complex subquotients

The map on a fixed filtration subquotient is a canonical cokernel map.  The statements below
expose its additive computations without requiring clients to unfold that universal construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory.HomologicalComplex.Filtered.Subquotient

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}
variable {K L : HomologicalComplex (FilteredObject C) c}

/-- A subquotient map sends the zero filtered-complex morphism to zero. -/
@[simp, stacks 0BKI "zero computation for filtered subquotient maps"]
theorem map_zero {p q : ℤ} (hpq : p ≤ q) :
    map (0 : K ⟶ L) hpq = 0 := sorry

/-- A subquotient map preserves addition of filtered-complex morphisms. -/
@[simp, stacks 0BKI "additive computation for filtered subquotient maps"]
theorem map_add (f g : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    map (f + g) hpq = map f hpq + map g hpq := sorry

/-- A subquotient map preserves negation of filtered-complex morphisms. -/
@[simp, stacks 0BKI "negation computation for filtered subquotient maps"]
theorem map_neg (f : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    map (-f) hpq = -map f hpq := sorry

/-- A subquotient map preserves subtraction of filtered-complex morphisms. -/
@[simp, stacks 0BKI "subtraction computation for filtered subquotient maps"]
theorem map_sub (f g : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    map (f - g) hpq = map f hpq - map g hpq := sorry

/-- A subquotient map preserves natural scalar multiplication. -/
@[simp, stacks 0BKI "natural-scalar computation for filtered subquotient maps"]
theorem map_nsmul (n : ℕ) (f : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    map (n • f) hpq = n • map f hpq := sorry

/-- A subquotient map preserves integer scalar multiplication. -/
@[simp, stacks 0BKI "integer-scalar computation for filtered subquotient maps"]
theorem map_zsmul (n : ℤ) (f : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    map (n • f) hpq = n • map f hpq := sorry

end CategoryTheory.HomologicalComplex.Filtered.Subquotient
