/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor.Right
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived
open CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X' X S' S : Scheme.{u}}
variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [KFlat.HomotopyTensorDescends X'.toRingedSpace]
variable [KFlat.TensorDescends X'.toRingedSpace]
variable [KFlat.IsLocalization X'.toRingedSpace]
variable (g' : X' ⟶ X)
variable [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
variable (T_X : @Right.Monoidal.Model
  (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
variable (T_X' : @Right.Monoidal.Model
  (RingedSpace.Modules X'.toRingedSpace) _ _ _ _ _ _ _)

/-- The canonical tensor base-change morphism, transported between the fixed-right derived
tensor model and the selected ambient monoidal models. -/
noncomputable def tensorBaseChangeMap
    (E K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') :
    (pullback g').obj (tensorObj E K) ⟶
      tensorObj ((pullback g').obj E) K' :=
  ObjectProperty.homMk
    ((pullback.inclusionIso g').hom.app (tensorObj E K) ≫
      (RingedSpace.modulePullbackDerived g'.toShHom).map
        (T_X.objIsoTensor E.obj K.obj).hom ≫
      (Functor.Monoidal.μIso
        (RingedSpace.modulePullbackDerived g'.toShHom) E.obj K.obj).symm.hom ≫
      ((pullback.inclusionIso g').inv.app E ⊗ₘ
        ((pullback.inclusionIso g').inv.app K ≫
          (ModuleDerived.Quasicoherent.inclusion X').map α)) ≫
      (T_X'.objIsoTensor ((pullback g').obj E).obj K'.obj).inv)

/-- After forgetting quasicoherence, the tensor base-change morphism is the pullback tensor
comparison followed by `𝟙 ⊗ₘ α`, with the fixed-right tensor models made explicit. -/
theorem tensorBaseChangeMap_obj
    (E K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') :
    (ModuleDerived.Quasicoherent.inclusion X').map
        (tensorBaseChangeMap g' T_X T_X' E K K' α) =
      (pullback.inclusionIso g').hom.app (tensorObj E K) ≫
        (RingedSpace.modulePullbackDerived g'.toShHom).map
          (T_X.objIsoTensor E.obj K.obj).hom ≫
        (Functor.Monoidal.μIso
          (RingedSpace.modulePullbackDerived g'.toShHom) E.obj K.obj).symm.hom ≫
        ((pullback.inclusionIso g').inv.app E ⊗ₘ
          ((pullback.inclusionIso g').inv.app K ≫
            (ModuleDerived.Quasicoherent.inclusion X').map α)) ≫
        (T_X'.objIsoTensor ((pullback g').obj E).obj K'.obj).inv := sorry

/-- Pointwise cohomology base change is preserved after derived tensoring by a complex with
quasicoherent cohomology. -/
theorem cohomologyBaseChange_tensor
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (E : ModuleDerived.Quasicoherent X)
    [∀ (x' : X') (i : ℤ), IsIso
      ((CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap K K' α x' i)] :
    ∀ (x' : X') (i : ℤ), IsIso
      ((CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap
        (tensorObj E K) (tensorObj ((pullback g').obj E) K')
        (tensorBaseChangeMap g' T_X T_X' E K K' α) x' i) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

end
