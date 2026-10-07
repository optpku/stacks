module

public import ReasLib.CategoryTheory.Sites.CostructuredArrowTopology
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cocontinuous comma-site comparisons

This file owns the sheaf-topos comparison for the topology on a costructured
arrow category.  The topology and the continuity of its projection are owned
by `CostructuredArrowTopology`; only the additional comma-to-slice data lives
here.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uC uD vC vD uA

namespace CategoryTheory.CostructuredArrow.CocontinuousOver

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) (V : D)

/-- The canonical functor from the cocontinuous comma site to the target slice site
is cocontinuous whenever `u` is. -/
instance toOver_isCocontinuous [u.IsCocontinuous J K] :
    Functor.IsCocontinuous (CostructuredArrow.toOver u V)
      (cocontinuousOverTopology J u V) (K.over V) := sorry

/-- The projection, the comma-to-slice functor, the original functor, and the slice
forgetful functor form a commutative square of categories. -/
theorem square_nonempty :
    Nonempty
      (CatCommSq
        (CostructuredArrow.proj u V)
        (CostructuredArrow.toOver u V)
        u
        (Over.forget V)) := sorry

/-- Lemma 7.28.5 (0D5R): the canonical comma/slice square gives the direct-image
comparison between the cocontinuous and continuous presentations. -/
@[stacks 0D5R]
theorem directImageComparison_nonempty
    [u.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ Type uA, u.op.HasPointwiseRightKanExtension F]
    [∀ F : (CostructuredArrow u V)ᵒᵖ ⥤ Type uA,
      (CostructuredArrow.toOver u V).op.HasPointwiseRightKanExtension F]
    [HasWeakSheafify (cocontinuousOverTopology J u V) (Type uA)]
    [HasWeakSheafify J (Type uA)] :
    Nonempty
      (Functor.sheafPushforwardContinuous (CostructuredArrow.proj u V) (Type uA)
          (cocontinuousOverTopology J u V) J ⋙
        Functor.sheafPushforwardCocontinuous (CostructuredArrow.toOver u V) (Type uA)
          (cocontinuousOverTopology J u V) (K.over V) ≅
      Functor.sheafPushforwardCocontinuous u (Type uA) J K ⋙
        Functor.sheafPushforwardContinuous (Over.forget V) (Type uA) (K.over V) K) := sorry

end CategoryTheory.CostructuredArrow.CocontinuousOver
