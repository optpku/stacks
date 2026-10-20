module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf

@[expose] public section

universe u v w w'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The constant sheaf with value `E` is the sheafification of the constant presheaf
with value `E`. -/
theorem constantSheaf_obj (J : GrothendieckTopology C) (D : Type w)
    [Category.{w'} D] [HasWeakSheafify J D] (E : D) :
    (constantSheaf J D).obj E =
      (presheafToSheaf J D).obj ((Functor.const Cᵒᵖ).obj E) := sorry

namespace Sheaf

/-- A sheaf is constant if and only if it is isomorphic to a constant sheaf. -/
theorem isConstant_iff_exists_iso (J : GrothendieckTopology C) {D : Type w}
    [Category.{w'} D] [HasWeakSheafify J D] (F : Sheaf J D) :
    Sheaf.IsConstant J F ↔ ∃ E : D, Nonempty (F ≅ (constantSheaf J D).obj E) := sorry

end Sheaf

end CategoryTheory
