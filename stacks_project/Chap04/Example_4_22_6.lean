module

public import ReasLib.CategoryTheory.Pro.Sequential.CommonRefinement
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory
namespace Pro

universe u v

variable {C : Type u} [Category.{v} C]
variable (X Y : ℕᵒᵖ ⥤ C)
variable (r r₁ r₂ : SequentialHom X Y)
variable (reindex' : ℕ →o ℕ) (hle : r.reindex ≤ reindex')

/- Example 4.22.6 (1): every sequential pro-morphism has a monotone level representative. -/
@[stacks 0G2W "existence of a monotone level representative"]
#check (CategoryTheory.Pro.SequentialHom.toHom_surjective (X := X) (Y := Y) :
  Function.Surjective
    (SequentialHom.toHom : SequentialHom X Y →
      ((Pro.lim (C := C) ℕᵒᵖ).obj X ⟶ (Pro.lim (C := C) ℕᵒᵖ).obj Y)))

/- Example 4.22.6 (2): monotone refinement does not change the represented pro-morphism. -/
@[stacks 0G2W "invariance under monotone refinement"]
#check (CategoryTheory.Pro.SequentialHom.toHom_refine r reindex' hle :
  (r.refine reindex' hle).toHom = r.toHom)

/- Example 4.22.6 (3): equality is detected after a common monotone refinement. -/
@[stacks 0G2W "equality detected on a common monotone refinement"]
#check (CategoryTheory.Pro.SequentialHom.toHom_eq_iff r₁ r₂ :
  r₁.toHom = r₂.toHom ↔ SequentialHom.Equivalent r₁ r₂)

end Pro
end CategoryTheory
