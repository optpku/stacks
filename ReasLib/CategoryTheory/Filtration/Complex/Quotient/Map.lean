module

public import ReasLib.CategoryTheory.Filtration.Complex.Quotient
public import ReasLib.CategoryTheory.Filtration.Quotient.Map
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Subquotient.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation for filtered-complex quotients

This facade lifts the category-independent quotient and subquotient computations to cochain
complexes.  The map is kept as the canonical functorial map rather than a newly bundled wrapper.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : FilteredComplex A}

/-- The identity filtered-complex map induces the identity on every quotient. -/
@[simp, stacks 0BKI "identity computation for filtered-complex quotient maps"]
theorem quotientMap_id (K : FilteredComplex A) (p : ℤ) :
    quotientMap (𝟙 K) p = 𝟙 (K.quotient p) := sorry

/-- Quotient maps preserve composition of filtered-complex morphisms. -/
@[simp, stacks 0BKI "composition computation for filtered-complex quotient maps"]
theorem quotientMap_comp {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M) (p : ℤ) :
    quotientMap (f ≫ g) p = quotientMap f p ≫ quotientMap g p := sorry

/-- A filtered-complex quotient map sends zero to zero. -/
@[simp, stacks 0BKI "zero computation for filtered-complex quotient maps"]
theorem quotientMap_zero (p : ℤ) :
    quotientMap (0 : K ⟶ L) p = 0 := sorry

/-- A filtered-complex quotient map preserves addition. -/
@[simp, stacks 0BKI "additive computation for filtered-complex quotient maps"]
theorem quotientMap_add (f g : K ⟶ L) (p : ℤ) :
    quotientMap (f + g) p = quotientMap f p + quotientMap g p := sorry

/-- A filtered-complex quotient map preserves negation. -/
@[simp, stacks 0BKI "negation computation for filtered-complex quotient maps"]
theorem quotientMap_neg (f : K ⟶ L) (p : ℤ) :
    quotientMap (-f) p = -quotientMap f p := sorry

/-- A filtered-complex quotient map preserves subtraction. -/
@[simp, stacks 0BKI "subtraction computation for filtered-complex quotient maps"]
theorem quotientMap_sub (f g : K ⟶ L) (p : ℤ) :
    quotientMap (f - g) p = quotientMap f p - quotientMap g p := sorry

/-- A filtered-complex quotient map preserves natural scalar multiplication. -/
@[simp, stacks 0BKI "natural-scalar computation for filtered-complex quotient maps"]
theorem quotientMap_nsmul (n : ℕ) (f : K ⟶ L) (p : ℤ) :
    quotientMap (n • f) p = n • quotientMap f p := sorry

/-- A filtered-complex quotient map preserves integer scalar multiplication. -/
@[simp, stacks 0BKI "integer-scalar computation for filtered-complex quotient maps"]
theorem quotientMap_zsmul (n : ℤ) (f : K ⟶ L) (p : ℤ) :
    quotientMap (n • f) p = n • quotientMap f p := sorry

/-- A filtered-complex subquotient map sends zero to zero. -/
@[simp, stacks 0BKI "zero computation for filtered-complex subquotient maps"]
theorem subquotientMap_zero {p q : ℤ} (hpq : p ≤ q) :
    subquotientMap (0 : K ⟶ L) hpq = 0 := sorry

/-- The identity filtered-complex map induces the identity on every subquotient. -/
@[simp, stacks 0BKI "identity computation for filtered-complex subquotient maps"]
theorem subquotientMap_id (K : FilteredComplex A) {p q : ℤ} (hpq : p ≤ q) :
    subquotientMap (𝟙 K) hpq = 𝟙 (K.subquotient hpq) := sorry

/-- Subquotient maps preserve composition of filtered-complex morphisms. -/
@[simp, stacks 0BKI "composition computation for filtered-complex subquotient maps"]
theorem subquotientMap_comp {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M)
    {p q : ℤ} (hpq : p ≤ q) :
    subquotientMap (f ≫ g) hpq = subquotientMap f hpq ≫ subquotientMap g hpq := sorry

/-- A filtered-complex subquotient map preserves addition. -/
@[simp, stacks 0BKI "additive computation for filtered-complex subquotient maps"]
theorem subquotientMap_add (f g : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    subquotientMap (f + g) hpq = subquotientMap f hpq + subquotientMap g hpq := sorry

/-- A filtered-complex subquotient map preserves negation. -/
@[simp, stacks 0BKI "negation computation for filtered-complex subquotient maps"]
theorem subquotientMap_neg (f : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    subquotientMap (-f) hpq = -subquotientMap f hpq := sorry

/-- A filtered-complex subquotient map preserves subtraction. -/
@[simp, stacks 0BKI "subtraction computation for filtered-complex subquotient maps"]
theorem subquotientMap_sub (f g : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    subquotientMap (f - g) hpq = subquotientMap f hpq - subquotientMap g hpq := sorry

/-- A filtered-complex subquotient map preserves natural scalar multiplication. -/
@[simp, stacks 0BKI "natural-scalar computation for filtered-complex subquotient maps"]
theorem subquotientMap_nsmul (n : ℕ) (f : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    subquotientMap (n • f) hpq = n • subquotientMap f hpq := sorry

/-- A filtered-complex subquotient map preserves integer scalar multiplication. -/
@[simp, stacks 0BKI "integer-scalar computation for filtered-complex subquotient maps"]
theorem subquotientMap_zsmul (n : ℤ) (f : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    subquotientMap (n • f) hpq = n • subquotientMap f hpq := sorry

end CategoryTheory.FilteredComplex
