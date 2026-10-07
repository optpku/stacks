module

public import ReasLib.CategoryTheory.Pretriangulated.Functor.Equivalence

/-!
# Weak generators and adjunctions

For a shift-compatible adjunction, a weak generator remains a weak generator after applying
the left adjoint precisely when the right adjoint reflects zero objects.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [HasZeroObject C] [HasZeroObject D]
variable [HasZeroMorphisms C] [HasZeroMorphisms D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable {F : C ⥤ D} {G : D ⥤ C}
variable [F.CommShift ℤ] [G.CommShift ℤ]

/-- If an object weakly generates the source of a shift-compatible adjunction, its image
weakly generates the target exactly when the right adjoint reflects zero objects. -/
theorem reflectsZero_iff_image_isWeakGenerator
    (adj : F ⊣ G) (E : C) (hE : IsWeakGenerator E) :
    (∀ K : D, IsZero (G.obj K) ↔ IsZero K) ↔ IsWeakGenerator (F.obj E) := sorry

end CategoryTheory.Adjunction
