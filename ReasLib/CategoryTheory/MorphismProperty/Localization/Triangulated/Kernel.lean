module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization

@[expose] public section

/-!
# Kernels of Triangulated Localizations

This leaf compares a triangulation-compatible morphism property with the cone-defined morphism
property associated to the kernel of its localization functor.
-/

universe v u

namespace CategoryTheory.MorphismProperty.Localization

open Limits ObjectProperty Pretriangulated

variable {C : Type u} [Category.{v} C]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (W : MorphismProperty C) [W.IsCompatibleWithTriangulation]

/-- passing from a triangulation-compatible morphism property to the kernel of its
localization and then taking the cone-defined property produces its canonical saturation. -/
@[stacks 05RL "saturation through a triangulated localization kernel"]
theorem kernel_trW_eq_saturation :
    (Functor.kernel W.Q).trW = (MorphismProperty.saturation (C := C)) W := sorry

/-- a saturated triangulation-compatible morphism property is recovered from the
kernel of its localization. -/
@[stacks 05RL "fixed points of the triangulated localization kernel"]
theorem kernel_trW_eq_self [W.IsSaturatedMultiplicativeSystem] :
    (Functor.kernel W.Q).trW = W := sorry


end CategoryTheory.MorphismProperty.Localization
