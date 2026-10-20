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

open Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- The objectwise kernel of a functor is unchanged when its codomain is
restricted to a full subcategory containing every object in its image and a
zero object of the ambient category (as a Serre subcategory does). -/
@[stacks 06XM "kernel invariance under lifting to a full subcategory"]
theorem lift_eq (P : ObjectProperty D) [P.ContainsZero] (F : C ⥤ D)
    (hF : ∀ X, P (F.obj X)) :
    Functor.kernel (P.lift F hF) = Functor.kernel F := by
  ext X
  constructor
  · intro hX
    obtain ⟨Z, hZ, hPZ⟩ := P.exists_prop_of_containsZero
    have hZ' : IsZero (⟨Z, hPZ⟩ : P.FullSubcategory) :=
      IsZero.of_full_of_faithful_of_isZero P.ι ⟨Z, hPZ⟩ hZ
    exact hZ.of_iso (P.ι.mapIso (hX.iso hZ'))
  · intro hX
    exact IsZero.of_full_of_faithful_of_isZero P.ι ((P.lift F hF).obj X) hX

end CategoryTheory.Functor.Kernel
