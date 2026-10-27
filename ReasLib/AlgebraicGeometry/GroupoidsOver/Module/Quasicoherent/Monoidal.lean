/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.FppfTensor
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Restriction

/-! # Symmetric monoidal quasi-coherent modules and their étale inclusion -/

@[expose] public section

-- Private comparison maps occur only in bodies of the public canonical constructions.
set_option backward.privateInPublic true

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite PresheafOfModules CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The fppf tensor unit is quasi-coherent. -/
theorem QCoh.unit_mem (X : GroupoidsOver S) [AlgebraicStack X] :
    quasiCoherentModuleProperty X (𝟙_ (RingedSite.ModuleCat.{u} (ringedSite X))) := sorry

/-- Quasi-coherence is stable under the ambient fppf unit and tensor. -/
instance QCoh.isMonoidal (X : GroupoidsOver S) [AlgebraicStack X] :
    (quasiCoherentModuleProperty X).IsMonoidal where
  prop_unit := QCoh.unit_mem X
  prop_tensor F G hF hG := (QCoh.Fppf.tensor ⟨F, hF⟩ ⟨G, hG⟩).property

/-- The inherited quasi-coherent tensor agrees with direct fppf tensor transport. -/
theorem QCoh.tensorObj_eq (X : GroupoidsOver S) [AlgebraicStack X] (F G : QCoh X) :
    (F ⊗ G : QCoh X) = QCoh.Fppf.tensor F G := rfl

/-- Identity-on-Γ comparison from the commutative-étale restriction of
`toComm F.obj` to the étale restriction of `F`. -/
private def QCoh.etaleOfCommRestrict_to_restriction {X : GroupoidsOver S}
    [AlgebraicStack X] (F : QCoh X) :
    etaleOfCommRestrict ((toCommFppfModules X).obj F.obj) ⟶
      (restriction X).obj F.obj where
  val :=
    { app := fun _ ↦ 𝟙 _
      naturality := sorry }

/-- Identity-on-Γ comparison from the étale restriction of `F` to the
commutative-étale restriction of `toComm F.obj`. -/
private def QCoh.restriction_to_etaleOfCommRestrict {X : GroupoidsOver S}
    [AlgebraicStack X] (F : QCoh X) :
    (restriction X).obj F.obj ⟶
      etaleOfCommRestrict ((toCommFppfModules X).obj F.obj) where
  val :=
    { app := fun _ ↦ 𝟙 _
      naturality := sorry }

/-- Identity-on-Γ comparison from the étale restriction of the transported
fppf tensor to the commutative-étale restriction of that tensor. -/
private def QCoh.restriction_tensor_to_etaleOfCommRestrict {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    ((QCoh.toLQCohFbc X).obj (QCoh.Fppf.tensor F G)).obj ⟶
      etaleOfCommRestrict (QCoh.Fppf.moduleTensor F G) where
  val :=
    { app := fun _ ↦ 𝟙 _
      naturality := sorry }

/-- Identity-on-Γ comparison from the commutative-étale restriction of the
transported fppf tensor to the étale restriction of that tensor. -/
private def QCoh.etaleOfCommRestrict_tensor_to_restriction {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    etaleOfCommRestrict (QCoh.Fppf.moduleTensor F G) ⟶
      ((QCoh.toLQCohFbc X).obj (QCoh.Fppf.tensor F G)).obj where
  val :=
    { app := fun _ ↦ 𝟙 _
      naturality := sorry }

/-- Pointwise tensor of commutative-étale restrictions compared with the
restricted pointwise tensor, at a section. -/
private def QCoh.restrictToCommEtaleVal_tensorObj_appIso {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) (U : X.totalᵒᵖ) :
    (Monoidal.tensorObj
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))).obj U ≅
      (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val).obj U :=
  tensorIso
    (restrictToCommEtaleVal_appIso ((toCommFppfModules X).obj F.obj) U)
    (restrictToCommEtaleVal_appIso ((toCommFppfModules X).obj G.obj) U)

/-- Lax restriction tensor comparison for the identity-on-Γ ring map, from the
pointwise tensor of commutative-étale restrictions to the restriction of the
pointwise fppf tensor. -/
private def QCoh.restrictToCommEtaleVal_tensorComparison {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    Monoidal.tensorObj
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj)) ⟶
      restrictPresheafToCommEtale X
        (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val) :=
  PresheafOfModules.Restriction.tensorComparison
    (commEtaleToFppfPresheaf X)
    ((toCommFppfModules X).obj F.obj).val
    ((toCommFppfModules X).obj G.obj).val

/-- `restrictToCommEtaleVal_tensorComparison` is the canonical restriction
tensor comparison. -/
private theorem QCoh.restrictToCommEtaleVal_tensorComparison_eq {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    QCoh.restrictToCommEtaleVal_tensorComparison F G =
      PresheafOfModules.Restriction.tensorComparison
        (commEtaleToFppfPresheaf X)
        ((toCommFppfModules X).obj F.obj).val
        ((toCommFppfModules X).obj G.obj).val :=
  rfl

/-- Oplax comparison from the restricted pointwise fppf tensor to the pointwise
tensor of commutative-étale restrictions, assembled from identity-restriction
isomorphisms. The ring map is `𝟙` on sections. -/
private def QCoh.restrictPresheafTensor_to_tensorObj {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    restrictPresheafToCommEtale X
        (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val) ⟶
      Monoidal.tensorObj
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj)) where
  app U :=
    (restrictPresheafToCommEtale_appIso
        (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val) U).hom ≫
      (QCoh.restrictToCommEtaleVal_tensorObj_appIso F G U).inv
  naturality := sorry

/-- The section of `restrictPresheafTensor_to_tensorObj` is the reverse of
`restrictPresheafToCommEtale_appIso` and the pointwise tensor iso. -/
private theorem QCoh.restrictPresheafTensor_to_tensorObj_app {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) (U : X.totalᵒᵖ) :
    (QCoh.restrictPresheafTensor_to_tensorObj F G).app U =
      (restrictPresheafToCommEtale_appIso
          (Monoidal.tensorObj
            ((toCommFppfModules X).obj F.obj).val
            ((toCommFppfModules X).obj G.obj).val) U).hom ≫
        (QCoh.restrictToCommEtaleVal_tensorObj_appIso F G U).inv :=
  rfl

/-- Unit comparison from étale sheafification of the restricted pointwise tensor
to the étale view of the fppf sheafification. -/
private def QCoh.sheafifyRestrict_to_etaleOfCommRestrictSheafification
    {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X) :
    (@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)).obj
        (restrictPresheafToCommEtale X
          (Monoidal.tensorObj
            ((toCommFppfModules X).obj F.obj).val
            ((toCommFppfModules X).obj G.obj).val)) ⟶
      etaleOfCommRestrict
        (associatedModuleTensor
          ((toCommFppfModules X).obj F.obj)
          ((toCommFppfModules X).obj G.obj)) :=
  (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
      (restrictPresheafToCommEtale X
        (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val))
      (etaleOfCommRestrict
        (associatedModuleTensor
          ((toCommFppfModules X).obj F.obj)
          ((toCommFppfModules X).obj G.obj)))).symm
    ((restrictScalars.{u} (presheafStructureMap (commEtaleToFppfPresheaf X))).map
      (@moduleSheafificationUnitToVal.{u + 1, u, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf) (associatedTopology_hasWeakSheafify X .fppf)
      (associatedTopology_wEqualsLocallyBijective X .fppf) (commAssociatedStructureSheaf X .fppf)
        (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val)))

/-- `sheafifyRestrict_to_etaleOfCommRestrictSheafification` is the sheafification
adjunct of restriction of the fppf sheafification unit. -/
private theorem QCoh.sheafifyRestrict_to_etaleOfCommRestrictSheafification_eq
    {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X) :
    QCoh.sheafifyRestrict_to_etaleOfCommRestrictSheafification F G =
      (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
          (restrictPresheafToCommEtale X
            (Monoidal.tensorObj
              ((toCommFppfModules X).obj F.obj).val
              ((toCommFppfModules X).obj G.obj).val))
          (etaleOfCommRestrict
            (associatedModuleTensor
              ((toCommFppfModules X).obj F.obj)
              ((toCommFppfModules X).obj G.obj)))).symm
        ((restrictScalars.{u} (presheafStructureMap (commEtaleToFppfPresheaf X))).map
          (@moduleSheafificationUnitToVal.{u + 1, u, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf) (associatedTopology_hasWeakSheafify X .fppf)
      (associatedTopology_wEqualsLocallyBijective X .fppf) (commAssociatedStructureSheaf X .fppf)
            (Monoidal.tensorObj
              ((toCommFppfModules X).obj F.obj).val
              ((toCommFppfModules X).obj G.obj).val))) :=
  rfl

/-- Adjunct of the restricted pointwise tensor comparison into the étale sheaf
tensor. -/
private def QCoh.sheafifyRestrict_to_tensorEtale {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    (@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)).obj
        (restrictPresheafToCommEtale X
          (Monoidal.tensorObj
            ((toCommFppfModules X).obj F.obj).val
            ((toCommFppfModules X).obj G.obj).val)) ⟶
      moduleTensorEtale
        (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))
        (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj)) :=
  (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
      (restrictPresheafToCommEtale X
        (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val))
      (moduleTensorEtale
        (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))
        (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj)))).symm
    (QCoh.restrictPresheafTensor_to_tensorObj F G ≫
      @moduleSheafificationUnitToVal.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
        (Monoidal.tensorObj
          (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
          (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))) ≫
      (Functor.Monoidal.μIso
          (@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X))
          (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
          (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))).inv.val ≫
      (moduleTensorMap.{u + 1, u, u}
        (@moduleSheafificationValIso.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
            (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))).hom
        (@moduleSheafificationValIso.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
            (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj))).hom).val)

/-- `sheafifyRestrict_to_tensorEtale` is the sheafification adjunct of the
restricted pointwise comparison followed by `μIso.inv` and
`moduleSheafificationValIso.hom` on the two factors. -/
private theorem QCoh.sheafifyRestrict_to_tensorEtale_eq {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    QCoh.sheafifyRestrict_to_tensorEtale F G =
      (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
          (restrictPresheafToCommEtale X
            (Monoidal.tensorObj
              ((toCommFppfModules X).obj F.obj).val
              ((toCommFppfModules X).obj G.obj).val))
          (moduleTensorEtale
            (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))
            (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj)))).symm
        (QCoh.restrictPresheafTensor_to_tensorObj F G ≫
          @moduleSheafificationUnitToVal.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
            (Monoidal.tensorObj
              (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
              (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))) ≫
          (Functor.Monoidal.μIso
              (@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X))
              (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
              (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))).inv.val ≫
          (moduleTensorMap.{u + 1, u, u}
            (@moduleSheafificationValIso.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
                (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))).hom
            (@moduleSheafificationValIso.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
                (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj))).hom).val) :=
  rfl

/-- Lax sheaf-tensor comparison from the étale sheaf tensor of commutative-étale
restrictions to étale sheafification of the restricted pointwise tensor. -/
private def QCoh.tensorEtale_to_sheafifyRestrict {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    moduleTensorEtale
        (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))
        (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj)) ⟶
      (@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)).obj
        (restrictPresheafToCommEtale X
          (Monoidal.tensorObj
            ((toCommFppfModules X).obj F.obj).val
            ((toCommFppfModules X).obj G.obj).val)) :=
  moduleTensorMap.{u + 1, u, u}
      (@moduleSheafificationValIso.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
          (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))).inv
      (@moduleSheafificationValIso.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
          (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj))).inv ≫
    (Functor.Monoidal.μIso
        (@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X))
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))).hom ≫
    (@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)).map
      (QCoh.restrictToCommEtaleVal_tensorComparison F G)

/-- `tensorEtale_to_sheafifyRestrict` is `moduleTensorMap` of
`moduleSheafificationValIso.inv`, then `μIso.hom`, then sheafification of
`restrictToCommEtaleVal_tensorComparison`. -/
private theorem QCoh.tensorEtale_to_sheafifyRestrict_eq {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    QCoh.tensorEtale_to_sheafifyRestrict F G =
      moduleTensorMap.{u + 1, u, u}
          (@moduleSheafificationValIso.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
              (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))).inv
          (@moduleSheafificationValIso.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)
              (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj))).inv ≫
        (Functor.Monoidal.μIso
            (@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X))
            (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
            (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))).hom ≫
        (@moduleSheafification.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)).map
          (QCoh.restrictToCommEtaleVal_tensorComparison F G) :=
  rfl

/-- Lax sheaf-tensor comparison
`etaleOfCommRestrict F ⊗ etaleOfCommRestrict G ⟶ etaleOfCommRestrict (F ⊗ G)`,
as the étale sheaf-tensor comparison into sheafification of the restricted
pointwise tensor, then the sheafification unit adjunct, then
`associatedModuleTensorIso.hom`. -/
private def QCoh.tensorEtale_to_etaleOfCommRestrict_moduleTensor
    {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X) :
    moduleTensorEtale
        (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))
        (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj)) ⟶
      etaleOfCommRestrict (QCoh.Fppf.moduleTensor F G) :=
  QCoh.tensorEtale_to_sheafifyRestrict F G ≫
    QCoh.sheafifyRestrict_to_etaleOfCommRestrictSheafification F G ≫
    etaleOfCommRestrictMap
      (associatedModuleTensorIso
        ((toCommFppfModules X).obj F.obj)
        ((toCommFppfModules X).obj G.obj)).hom

/-- `tensorEtale_to_etaleOfCommRestrict_moduleTensor` is
`tensorEtale_to_sheafifyRestrict`, then the unit adjunct, then
`associatedModuleTensorIso.hom`. -/
private theorem QCoh.tensorEtale_to_etaleOfCommRestrict_moduleTensor_eq
    {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X) :
    QCoh.tensorEtale_to_etaleOfCommRestrict_moduleTensor F G =
      QCoh.tensorEtale_to_sheafifyRestrict F G ≫
        QCoh.sheafifyRestrict_to_etaleOfCommRestrictSheafification F G ≫
        etaleOfCommRestrictMap
          (associatedModuleTensorIso
            ((toCommFppfModules X).obj F.obj)
            ((toCommFppfModules X).obj G.obj)).hom :=
  rfl

/-- Underlying étale morphism of the lax tensorator
`i(F) ⊗ i(G) ⟶ i(F ⊗ G)`, as a forward composite of identity-on-Γ
comparisons with the sheaf-tensor comparison. -/
def QCoh.toLQCohFbc_tensorator_hom {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : QCoh X) :
    (LQCohFbc.tensor
        ((QCoh.toLQCohFbc X).obj F) ((QCoh.toLQCohFbc X).obj G)).obj ⟶
      ((QCoh.toLQCohFbc X).obj (QCoh.Fppf.tensor F G)).obj :=
  moduleTensorMap.{u + 1, u, u}
      (QCoh.restriction_to_etaleOfCommRestrict F)
      (QCoh.restriction_to_etaleOfCommRestrict G) ≫
    QCoh.tensorEtale_to_etaleOfCommRestrict_moduleTensor F G ≫
    QCoh.etaleOfCommRestrict_tensor_to_restriction F G

/-- Lax tensorator `i(F) ⊗ i(G) ⟶ i(F ⊗ G)` of `QCoh.toLQCohFbc`. The
source is the étale tensor of the images. -/
def QCoh.toLQCohFbc_tensorator {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : QCoh X) :
    LQCohFbc.tensor
        ((QCoh.toLQCohFbc X).obj F) ((QCoh.toLQCohFbc X).obj G) ⟶
      (QCoh.toLQCohFbc X).obj (QCoh.Fppf.tensor F G) :=
  ObjectProperty.homMk (QCoh.toLQCohFbc_tensorator_hom F G)

/-- The underlying étale morphism of `toLQCohFbc_tensorator` is
`toLQCohFbc_tensorator_hom`. -/
theorem QCoh.toLQCohFbc_tensorator_hom_eq {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    (QCoh.toLQCohFbc_tensorator F G).hom =
      QCoh.toLQCohFbc_tensorator_hom F G :=
  rfl


namespace QCoh

variable {X : GroupoidsOver S} [AlgebraicStack X]

/-- The actual étale tensor of the two included quasi-coherent modules is
an fppf sheaf by local quasi-coherence and flat base change. -/
private theorem targetTensor_isFppfSheaf (F G : QCoh X) :
    Presheaf.IsSheaf (inheritedFppfTopology X)
      (fppfViewPresheaf (LQCohFbc.tensor
        ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G)).obj).presheaf := by
  exact @isSheaf_fppf_of_lqcohFbc _ _ _
    ((LQCohFbc.tensor ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G)).obj)
    (LQCohFbc.tensor ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G)).property.1
    (LQCohFbc.tensor ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G)).property.2

/-- A presheaf map from pure tensors into the actual target étale tensor. -/
private def pointwiseToEtaleTensor (F G : QCoh X) :
    restrictPresheafToCommEtale X
      (Monoidal.tensorObj ((toCommFppfModules X).obj F.obj).val
        ((toCommFppfModules X).obj G.obj).val) ⟶
      (LQCohFbc.tensor ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G)).obj.val :=
  (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X)
      (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X) _ _)
      (sheafifyRestrict_to_tensorEtale F G) ≫
    (moduleTensorMap.{u + 1, u, u}
      (etaleOfCommRestrict_to_restriction F) (etaleOfCommRestrict_to_restriction G)).val

/-- Forward descent of the fppf tensor to the actual étale tensor. -/
def toLQCohFbc_tensoratorOplaxHom (F G : QCoh X) :
    ((toLQCohFbc X).obj (Fppf.tensor F G)).obj ⟶
      (LQCohFbc.tensor ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G)).obj :=
  restriction_tensor_to_etaleOfCommRestrict F G ≫
    etaleOfCommRestrictMap
      (associatedModuleTensorIso ((toCommFppfModules X).obj F.obj)
        ((toCommFppfModules X).obj G.obj)).inv ≫
    descendToEtale _ (targetTensor_isFppfSheaf F G) _ (pointwiseToEtaleTensor F G)

/-- The reverse tensor comparison in `LQCohFbc`, whose underlying map descends
the pointwise tensor map from fppf sheafification to the étale tensor. -/
def toLQCohFbc_tensoratorOplax (F G : QCoh X) :
    (toLQCohFbc X).obj (Fppf.tensor F G) ⟶
      LQCohFbc.tensor ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G) :=
  CategoryTheory.ObjectProperty.homMk (toLQCohFbc_tensoratorOplaxHom F G)


/-- The forward and reverse inclusion tensor comparisons are inverse. -/
theorem toLQCohFbc_tensorator_inverse_laws (F G : QCoh X) :
    (toLQCohFbc_tensorator F G ≫ toLQCohFbc_tensoratorOplax F G = 𝟙 _) ∧
    (toLQCohFbc_tensoratorOplax F G ≫ toLQCohFbc_tensorator F G = 𝟙 _) := sorry

/-- The inclusion tensor comparison with its explicitly descended inverse. -/
def toLQCohFbc_tensorIso (F G : QCoh X) :
    LQCohFbc.tensor ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G) ≅
      (toLQCohFbc X).obj (Fppf.tensor F G) where
  hom := toLQCohFbc_tensorator F G
  inv := toLQCohFbc_tensoratorOplax F G
  hom_inv_id := (toLQCohFbc_tensorator_inverse_laws F G).1
  inv_hom_id := (toLQCohFbc_tensorator_inverse_laws F G).2

/-- The canonical tensor comparison of the inclusion is invertible. -/
instance toLQCohFbc_tensorator_isIso (F G : QCoh X) :
    IsIso (toLQCohFbc_tensorator F G) := (toLQCohFbc_tensorIso F G).isIso_hom

/-- Restricting the transported fppf structure module gives the étale structure module. -/
private def structureModuleComparison :
    @unitModule.{u + 1, u, u} X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (commEtaleStructureSheaf X) ≅
      (restriction X).obj ((fromCommFppfModules X).obj
        (@unitModule.{u + 1, u, u} X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf) (commAssociatedStructureSheaf X .fppf))) where
  hom := { val := { app := fun _ => 𝟙 _, naturality := by intros; rfl } }
  inv := { val := { app := fun _ => 𝟙 _, naturality := by intros; rfl } }
  hom_inv_id := by ext U; rfl
  inv_hom_id := by ext U; rfl

/-- The inclusion identifies the étale and fppf tensor units through structure modules. -/
def toLQCohFbc_unitIso (X : GroupoidsOver S) [AlgebraicStack X] :
    𝟙_ (LQCohFbc X) ≅ (toLQCohFbc X).obj (𝟙_ (QCoh X)) :=
  (lqcohFbc X).isoMk
    ((@unitIsoTensorUnit.{u + 1, u, u}
      X.total inferInstance (X.etaleTopology)
      (etaleTopology_hasSheafCompose_commRing X) (etaleTopology_hasWeakSheafify X) (etaleTopology_wEqualsLocallyBijective X) (commEtaleStructureSheaf X)).symm ≪≫
      structureModuleComparison ≪≫
      (restriction X).mapIso ((fromCommFppfModules X).mapIso
        (@unitIsoTensorUnit.{u + 1, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf) (associatedTopology_hasWeakSheafify X .fppf) (associatedTopology_wEqualsLocallyBijective X .fppf) (commAssociatedStructureSheaf X .fppf))))

/-- The inclusion preserves unit and tensor coherently with the prescribed comparisons. -/
def toLQCohFbc_coreMonoidal (X : GroupoidsOver S) [AlgebraicStack X] :
    (toLQCohFbc X).CoreMonoidal := by
  refine {
    εIso := toLQCohFbc_unitIso X
    μIso := toLQCohFbc_tensorIso
    μIso_hom_natural_left := ?_
    μIso_hom_natural_right := ?_
    associativity := ?_
    left_unitality := ?_
    right_unitality := ?_ }
  all_goals sorry

/-- The canonical inclusion of quasi-coherent modules is strong monoidal. -/
instance toLQCohFbc_monoidal (X : GroupoidsOver S) [AlgebraicStack X] :
    (toLQCohFbc X).Monoidal := (toLQCohFbc_coreMonoidal X).toMonoidal

/-- The inclusion preserves the symmetry of module tensor products. -/
instance toLQCohFbc_braided (X : GroupoidsOver S) [AlgebraicStack X] :
    (toLQCohFbc X).Braided where
  braided := sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
