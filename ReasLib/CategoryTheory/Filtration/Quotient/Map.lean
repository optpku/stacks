module

public import ReasLib.CategoryTheory.Filtration.Functors
public import ReasLib.CategoryTheory.Filtration.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation for filtration quotient maps

The quotient functor is owned by `Filtration.Functors`.  This leaf keeps the additive
computations of its induced maps next to that owner, so clients do not have to unfold a
cokernel-map construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
variable {X Y : FilteredObject C}

/-- A quotient map preserves addition of filtered morphisms. -/
@[simp, stacks 0121 "additive computation for filtration quotient maps"]
theorem quotientMap_add (f g : X ⟶ Y) (p : ℤ) :
    (f + g).quotientMap p = f.quotientMap p + g.quotientMap p := sorry

/-- A quotient map preserves negation of filtered morphisms. -/
@[simp, stacks 0121 "negation computation for filtration quotient maps"]
theorem quotientMap_neg (f : X ⟶ Y) (p : ℤ) :
    (-f).quotientMap p = -f.quotientMap p := sorry

/-- A quotient map preserves subtraction of filtered morphisms. -/
@[simp, stacks 0121 "subtraction computation for filtration quotient maps"]
theorem quotientMap_sub (f g : X ⟶ Y) (p : ℤ) :
    (f - g).quotientMap p = f.quotientMap p - g.quotientMap p := sorry

/-- A quotient map preserves natural scalar multiplication. -/
@[simp, stacks 0121 "natural-scalar computation for filtration quotient maps"]
theorem quotientMap_nsmul (n : ℕ) (f : X ⟶ Y) (p : ℤ) :
    (n • f).quotientMap p = n • f.quotientMap p := sorry

/-- A quotient map preserves integer scalar multiplication. -/
@[simp, stacks 0121 "integer-scalar computation for filtration quotient maps"]
theorem quotientMap_zsmul (n : ℤ) (f : X ⟶ Y) (p : ℤ) :
    (n • f).quotientMap p = n • f.quotientMap p := sorry

end CategoryTheory.FilteredObject.Hom
