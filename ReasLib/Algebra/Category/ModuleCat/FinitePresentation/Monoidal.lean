/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Module.FinitePresentation.TensorProduct

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ObjectProperty

universe uR uM

namespace ModuleCat

variable (R : Type uR) [CommRing R]

/-- The tensor product and ULift unit give the usual monoidal data on modules
whose universe is at least the universe of the coefficient ring. -/
instance instMonoidalCategoryStructMax :
    MonoidalCategoryStruct (ModuleCat.{max uR uM} R) where
  tensorObj M N := of R (TensorProduct R M N)
  whiskerLeft M _ _ f := ofHom <| f.hom.lTensor M
  whiskerRight f M := ofHom <| f.hom.rTensor M
  tensorHom f g := ofHom <| TensorProduct.map f.hom g.hom
  tensorUnit := of R (ULift.{uM, uR} R)
  associator M N K := (TensorProduct.assoc R M N K).toModuleIso
  leftUnitor M :=
    (((TensorProduct.congr
          (ULift.moduleEquiv : ULift.{uM, uR} R ≃ₗ[R] R)
          (LinearEquiv.refl R M)).trans
        (TensorProduct.lid R M)).toModuleIso)
  rightUnitor M :=
    (((TensorProduct.congr
          (LinearEquiv.refl R M)
          (ULift.moduleEquiv : ULift.{uM, uR} R ≃ₗ[R] R)).trans
        (TensorProduct.rid R M)).toModuleIso)

/-- The tensor-product monoidal category structure on modules at the maximum
of the coefficient-ring and module universes. -/
instance instMonoidalCategoryMax :
    MonoidalCategory (ModuleCat.{max uR uM} R) where
  tensorHom_def := sorry
  id_tensorHom_id := sorry
  tensorHom_comp_tensorHom := sorry
  whiskerLeft_id := sorry
  id_whiskerRight := sorry
  associator_naturality := sorry
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  pentagon := sorry
  triangle := sorry

namespace isFinitePresentation

/-- Tensor products of finitely presented modules remain finitely presented. -/
theorem prop_tensor {M N : ModuleCat.{max uR uM} R}
    (hM : isFinitePresentation.{uR, max uR uM} R M)
    (hN : isFinitePresentation.{uR, max uR uM} R N) :
    isFinitePresentation.{uR, max uR uM} R
      (ModuleCat.of R (TensorProduct R M N)) := sorry

/-- The full subcategory of finitely presented modules is monoidal under the
usual tensor product. -/
instance instIsMonoidal :
    (isFinitePresentation.{uR, max uR uM} R).IsMonoidal := sorry

end isFinitePresentation

end ModuleCat
