module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

@[expose] public section

/-!
# Kernels of Functors Lifted to Full Subcategories

Lifting a functor through a full subcategory does not change which source
objects it sends to zero objects.
-/

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor.Kernel

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- The objectwise kernel of a functor is unchanged when its codomain is
restricted to a full subcategory containing every object in its image. -/
@[stacks 06XM "kernel invariance under lifting to a full subcategory"]
theorem lift_eq (P : ObjectProperty D) (F : C ⥤ D)
    (hF : ∀ X, P (F.obj X)) :
    Functor.kernel (P.lift F hF) = Functor.kernel F := sorry

end CategoryTheory.Functor.Kernel
