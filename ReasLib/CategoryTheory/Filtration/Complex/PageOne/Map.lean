module

public import ReasLib.CategoryTheory.Filtration.Complex.PageOne
public import ReasLib.CategoryTheory.Filtration.Complex.PageOne.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation for the boundary-model first-page functor

This leaf records the additive computations for the explicit first-page map and its bidegree
components. The boundary construction and its comparison theorems remain in `PageOne.lean`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.Page.One

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : FilteredComplex C}

/-- A boundary-model first-page component sends zero to zero. -/
@[simp, stacks 012N "zero computation for boundary-model first-page components"]
theorem mapComponent_zero (pq : ℤ × ℤ) : mapComponent (0 : K ⟶ L) pq = 0 := sorry

/-- A boundary-model first-page component preserves addition. -/
@[simp, stacks 012N "addition computation for boundary-model first-page components"]
theorem mapComponent_add (f g : K ⟶ L) (pq : ℤ × ℤ) :
    mapComponent (f + g) pq = mapComponent f pq + mapComponent g pq := sorry

/-- A boundary-model first-page component preserves negation. -/
@[simp, stacks 012N "negation computation for boundary-model first-page components"]
theorem mapComponent_neg (f : K ⟶ L) (pq : ℤ × ℤ) :
    mapComponent (-f) pq = -mapComponent f pq := sorry

/-- A boundary-model first-page component preserves subtraction. -/
@[simp, stacks 012N "subtraction computation for boundary-model first-page components"]
theorem mapComponent_sub (f g : K ⟶ L) (pq : ℤ × ℤ) :
    mapComponent (f - g) pq = mapComponent f pq - mapComponent g pq := sorry

/-- A boundary-model first-page component preserves natural scalar multiplication. -/
@[simp, stacks 012N "natural-scalar computation for boundary-model first-page components"]
theorem mapComponent_nsmul (n : ℕ) (f : K ⟶ L) (pq : ℤ × ℤ) :
    mapComponent (n • f) pq = n • mapComponent f pq := sorry

/-- A boundary-model first-page component preserves integer scalar multiplication. -/
@[simp, stacks 012N "integer-scalar computation for boundary-model first-page components"]
theorem mapComponent_zsmul (n : ℤ) (f : K ⟶ L) (pq : ℤ × ℤ) :
    mapComponent (n • f) pq = n • mapComponent f pq := sorry

/-- The boundary-model first-page map sends zero to zero. -/
@[simp, stacks 012N "zero computation for boundary-model first-page maps"]
theorem map_zero : map (0 : K ⟶ L) = 0 := sorry

/-- The boundary-model first-page map preserves addition. -/
@[simp, stacks 012N "addition computation for boundary-model first-page maps"]
theorem map_add (f g : K ⟶ L) : map (f + g) = map f + map g := sorry

/-- The boundary-model first-page map preserves negation. -/
@[simp, stacks 012N "negation computation for boundary-model first-page maps"]
theorem map_neg (f : K ⟶ L) : map (-f) = -map f := sorry

/-- The boundary-model first-page map preserves subtraction. -/
@[simp, stacks 012N "subtraction computation for boundary-model first-page maps"]
theorem map_sub (f g : K ⟶ L) : map (f - g) = map f - map g := sorry

/-- The boundary-model first-page map preserves natural scalar multiplication. -/
@[simp, stacks 012N "natural-scalar computation for boundary-model first-page maps"]
theorem map_nsmul (n : ℕ) (f : K ⟶ L) : map (n • f) = n • map f := sorry

/-- The boundary-model first-page map preserves integer scalar multiplication. -/
@[simp, stacks 012N "integer-scalar computation for boundary-model first-page maps"]
theorem map_zsmul (n : ℤ) (f : K ⟶ L) : map (n • f) = n • map f := sorry

end CategoryTheory.FilteredComplex.Page.One
