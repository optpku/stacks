module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe uC vC uD vD uE vE

namespace CategoryTheory.ModulesOnCategory.QuasiCoherent

section


variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : C → Type uE} [∀ U, Category.{vE} (E U)]
variable (RΓ : ∀ U : C, D ⥤ E U)
variable (restrict : ∀ {U V : C}, (U ⟶ V) → E V ⥤ E U)
variable
  (comparison : ∀ {U V : C} (f : U ⟶ V),
    RΓ V ⋙ restrict f ⟶ RΓ U)

/- Definition 24.33.1: `QC(𝒜,d)` is modeled by the full subcategory cut out by the canonical
sectionwise comparison maps. The generic owner allows the fibers `E U` to be intrinsic derived
categories of DG modules, ordinary module-derived categories, or any later equivalent model. -/
@[stacks 0GZ9] #check
  (Objects RΓ restrict comparison : Type uD)

/- The underlying object property requires every sectionwise comparison map to be invertible. -/
#check (property RΓ restrict comparison : ObjectProperty D)

/- Membership has a pointwise comparison-isomorphism specification. -/
#check @mem_iff

/- Every object of the full subcategory supplies all comparison-isomorphism instances. -/
#check @isIso_comparison

end


end CategoryTheory.ModulesOnCategory.QuasiCoherent
