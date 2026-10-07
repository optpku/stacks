module

public import Mathlib.CategoryTheory.Sites.Coverage

/-!
# Refinement of presieve sheaf conditions

This leaf contains the topology-independent refinement API for set-valued
presheaves. Fixed-target family bridges belong in
`ReasLib.CategoryTheory.Sites.Family.Sheaf.Refinement`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Presieve

variable {C : Type u} [Category.{v} C]

/-- Separatedness transfers from `R` to `S` when every arrow of `R` factors
through an arrow of `S`. -/
theorem IsSeparatedFor.of_factorsThru
    {U : C} {F : Cᵒᵖ ⥤ Type w} {R S : Presieve U}
    (hR : R.IsSeparatedFor F) (hRS : R.FactorsThru S) :
    S.IsSeparatedFor F := sorry

/-- The sheaf condition for a presieve depends only on its generated sieve. -/
theorem isSheafFor_iff_of_generate_eq
    {U : C} {F : Cᵒᵖ ⥤ Type w} {R S : Presieve U}
    (h : Sieve.generate R = Sieve.generate S) :
    R.IsSheafFor F ↔ S.IsSheafFor F := sorry

end CategoryTheory.Presieve
