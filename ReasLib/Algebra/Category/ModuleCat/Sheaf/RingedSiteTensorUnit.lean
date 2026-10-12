/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TensorUnit
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor unit on a ringed site

This module specializes the generic tensor-unit comparison to modules over a
commutative ring sheaf on an arbitrary site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

/-- The canonical morphism from the ambient tensor unit to the structure module.  Unlike taking
the inverse of `unitIsoTensorUnit` through `IsIso`, this definition exposes the two structural
maps that construct the comparison. -/
@[stacks 03L6 "tensor unit to structure module"]
noncomputable def tensorUnitToUnitModule :
    (𝟙_ (ringedSiteModuleCategory.{u, v, w, w} J 𝒪)) ⟶ unitModule J 𝒪 :=
  (Functor.Monoidal.εIso
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj))).hom ≫
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J 𝒪).obj)).counit.app (unitModule J 𝒪)

/-- The named inverse from the structure module back to the ambient tensor unit. -/
@[stacks 03L6 "structure module to tensor unit"]
noncomputable def unitModuleToTensorUnit :
    (unitModule J 𝒪 : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) ⟶
      (𝟙_ (ringedSiteModuleCategory.{u, v, w, w} J 𝒪)) :=
  @CategoryTheory.inv _ _ _ _
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringSheaf J 𝒪).obj)).counit.app (unitModule J 𝒪))
      (NatIso.isIso_app_of_isIso
        (PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringSheaf J 𝒪).obj)).counit (unitModule J 𝒪)) ≫
    (Functor.Monoidal.εIso
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj))).symm.hom

/-- The tensor-unit comparison followed by its named inverse is the identity. -/
@[simp, stacks 03L6 "tensor unit comparison forward-inverse law"]
theorem tensorUnitToUnitModule_hom_inv_id :
    tensorUnitToUnitModule (J := J) (𝒪 := 𝒪) ≫
        unitModuleToTensorUnit (J := J) (𝒪 := 𝒪) = 𝟙 _ := by
  dsimp only [ringedSiteModuleCategory]
  unfold tensorUnitToUnitModule unitModuleToTensorUnit
  rw (config := { transparency := .all }) [Category.assoc]
  rw (config := { transparency := .all }) [@IsIso.hom_inv_id_assoc _ _ _ _ _
    (NatIso.isIso_app_of_isIso
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringSheaf J 𝒪).obj)).counit (unitModule J 𝒪))]
  exact (Functor.Monoidal.εIso
    (PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj))).hom_inv_id

/-- The named inverse followed by the tensor-unit comparison is the identity. -/
@[simp, stacks 03L6 "tensor unit comparison inverse-forward law"]
theorem tensorUnitToUnitModule_inv_hom_id :
    unitModuleToTensorUnit (J := J) (𝒪 := 𝒪) ≫
        tensorUnitToUnitModule (J := J) (𝒪 := 𝒪) = 𝟙 _ := by
  dsimp only [ringedSiteModuleCategory]
  unfold tensorUnitToUnitModule unitModuleToTensorUnit
  rw (config := { transparency := .all }) [Category.assoc]
  rw (config := { transparency := .all }) [(Functor.Monoidal.εIso
    (PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj))).inv_hom_id_assoc]
  exact @IsIso.inv_hom_id _ _ _ _ _
    (NatIso.isIso_app_of_isIso
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringSheaf J 𝒪).obj)).counit (unitModule J 𝒪))

/-- The structure module of a ringed site is canonically isomorphic to the ambient tensor unit,
with both morphisms given by the structural sheafification and monoidal-unit maps. -/
@[stacks 03L6 "tensor unit of module sheaves"]
noncomputable def unitIsoTensorUnit :
    (unitModule J 𝒪 : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) ≅
      (𝟙_ (ringedSiteModuleCategory.{u, v, w, w} J 𝒪)) where
  hom := unitModuleToTensorUnit (J := J) (𝒪 := 𝒪)
  inv := tensorUnitToUnitModule (J := J) (𝒪 := 𝒪)
  hom_inv_id := tensorUnitToUnitModule_inv_hom_id (J := J) (𝒪 := 𝒪)
  inv_hom_id := tensorUnitToUnitModule_hom_inv_id (J := J) (𝒪 := 𝒪)

/-- The explicit tensor-unit comparison is invertible because it is the inverse component of the
named tensor-unit isomorphism. -/
@[stacks 03L6 "tensor unit comparison is invertible"]
theorem tensorUnitToUnitModule_isIso :
    IsIso (tensorUnitToUnitModule (J := J) (𝒪 := 𝒪)) :=
  (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).isIso_inv

/-- The forward morphism of `unitIsoTensorUnit` is the named map from the structure module to
the tensor unit. -/
@[simp, stacks 03L6 "tensor unit isomorphism forward map"]
theorem unitIsoTensorUnit_hom :
    (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).hom =
      unitModuleToTensorUnit (J := J) (𝒪 := 𝒪) := rfl

/-- The inverse morphism of `unitIsoTensorUnit` is the explicit tensor-unit comparison. -/
@[simp, stacks 03L6 "tensor unit isomorphism inverse map"]
theorem unitIsoTensorUnit_inv :
    (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).inv =
      tensorUnitToUnitModule (J := J) (𝒪 := 𝒪) := rfl

/-- The explicit tensor-unit comparison is the inverse of `unitIsoTensorUnit`. -/
@[simp, stacks 03L6 "tensor unit comparison inverse bridge"]
theorem tensorUnitToUnitModule_eq :
    tensorUnitToUnitModule (J := J) (𝒪 := 𝒪) =
      (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).inv := rfl

/-- The structure module is tensor-invertible on every ringed site with the canonical
tensor-unit comparison. -/
@[stacks 03L6 "tensor unit is invertible"]
noncomputable def unitModuleIsInvertible :
    MonoidalCategory.isInvertibleObject
      (unitModule J 𝒪 : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :=
  MonoidalCategory.isInvertibleObject.of_iso
    (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).symm inferInstance

end SheafOfModules.RingedSite
