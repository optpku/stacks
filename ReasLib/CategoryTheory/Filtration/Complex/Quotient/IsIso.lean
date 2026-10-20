module

public import ReasLib.CategoryTheory.Filtration.Complex.Quotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism transport for filtered-complex quotients

Quotient and subquotient maps inherit isomorphisms from a filtered-complex isomorphism.  The
component instances are exposed explicitly because degreewise arguments are the common use case.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : FilteredComplex A}

/-- A quotient map is an isomorphism when the filtered-complex map is. -/
@[stacks 0BKI "isomorphism of filtered-complex quotient maps"]
noncomputable instance quotientMap_isIso (f : K ⟶ L) (p : ℤ) [IsIso f] :
    IsIso (quotientMap f p) := sorry

/-- Every degree component of a quotient map is an isomorphism when the source map is. -/
@[stacks 0BKI "isomorphism on filtered-complex quotient components"]
noncomputable instance quotientMap_f_isIso (f : K ⟶ L) (p n : ℤ) [IsIso f] :
    IsIso ((quotientMap f p).f n) := sorry

/-- A subquotient map is an isomorphism when the filtered-complex map is. -/
@[stacks 0BKI "isomorphism of filtered-complex subquotient maps"]
noncomputable instance subquotientMap_isIso (f : K ⟶ L) {p q : ℤ} (hpq : p ≤ q)
    [IsIso f] : IsIso (subquotientMap f hpq) := sorry

/-- Every degree component of a subquotient map is an isomorphism when the source map is. -/
@[stacks 0BKI "isomorphism on filtered-complex subquotient components"]
noncomputable instance subquotientMap_f_isIso (f : K ⟶ L) (n : ℤ) {p q : ℤ} (hpq : p ≤ q)
    [IsIso f] : IsIso ((subquotientMap f hpq).f n) := sorry

variable (f : K ⟶ L) [IsIso f]
#synth IsIso (quotientMap f 0)
#synth IsIso ((quotientMap f 0).f 0)
#synth IsIso (subquotientMap f (le_refl (0 : ℤ)))
#synth IsIso ((subquotientMap f (le_refl (0 : ℤ))).f 0)

end CategoryTheory.FilteredComplex
