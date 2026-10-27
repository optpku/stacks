/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.RingedComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module.EtaleGrothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TensorScalarExtension
public import ReasLib.CategoryTheory.Sites.Topos.InternalCommRing
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.RingTheory.FreeRing

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

/-! # Module functors of a spaces-étale augmentation -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open Functor
open RingedSite RingedSite.ToposHom
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

/-- Ring elements are represented by the free ring on one generator. -/
private def coefficientRingForgetIso :
    coyoneda.obj (Opposite.op (RingCat.of (FreeRing PUnit.{u + 1}))) ≅
      forget RingCat.{u} :=
  NatIso.ofComponents (fun R ↦ Equiv.toIso
    { toFun := fun f ↦ f.hom (FreeRing.of PUnit.unit)
      invFun := fun r ↦ RingCat.ofHom (FreeRing.lift (fun _ ↦ r))
      left_inv := fun f ↦ by
        apply RingCat.hom_ext
        apply FreeRing.hom_ext
        intro x
        cases x
        exact FreeRing.lift_of _ _
      right_inv := fun r ↦ FreeRing.lift_of _ _ })
    (fun f ↦ by ext g; rfl)

/-- The underlying-ring-set functor preserves all limits used on the étale sites. -/
private instance coefficientRingForgetPreservesLimits :
    Limits.PreservesLimitsOfSize.{u + 1, u + 1} (forget RingCat.{u}) :=
  Limits.preservesLimits_of_natIso coefficientRingForgetIso

/-- A limiting cone of underlying sets already bounds its own ring of sections. -/
private instance coefficientRingForgetReflectsLimits :
    Limits.ReflectsLimitsOfSize.{u + 1, u + 1} (forget RingCat.{u}) where
  reflectsLimitsOfShape := { reflectsLimit := fun {F} ↦
    { reflects := fun {s} hs ↦ by
        -- Local instance justification (proof-local temporary data): the given cone supplies its own set-valued limit, rather than a bound on arbitrary large diagrams.
        letI : Limits.HasLimit (F ⋙ forget RingCat.{u}) := ⟨_, hs⟩
        -- Local instance justification (proof-local temporary data): the limiting section type is small because it is isomorphic to this cone's small carrier.
        letI : Small.{u} (F ⋙ forget RingCat.{u}).sections :=
          (Limits.Types.hasLimit_iff_small_sections _).mp inferInstance
        exact (Limits.reflectsLimit_of_reflectsIsomorphisms F
          (forget RingCat.{u})).reflects hs } }

/-- Forgetting commutativity preserves the limits used on the spaces-étale sites. -/
private instance coefficientCommForgetPreservesLimits :
    Limits.PreservesLimitsOfSize.{u + 1, u + 1} (forget₂ CommRingCat.{u} RingCat.{u}) := by
  -- Local instance justification (defeq pin): the composite underlying-set functor is the commutative-ring forgetful right adjoint, which preserves arbitrary existing limits.
  letI : Limits.PreservesLimitsOfSize.{u + 1, u + 1}
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget RingCat.{u}) :=
    inferInstanceAs (Limits.PreservesLimitsOfSize.{u + 1, u + 1} (forget CommRingCat.{u}))
  exact Limits.preservesLimits_of_reflects_of_preserves _ (forget RingCat.{u})

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Sections of the spaces-étale structure sheaf form commutative rings. -/
private theorem spacesCoefficientComm (V : (spacesEtaleSite X)ᵒᵖ)
    (x y : (spacesStructureSheaf X).obj.obj V) : x * y = y * x := by
  let e := Iso.ringCatIsoToRingEquiv
    (asIso (Etale.Big.spacesStructureToGamma V.unop) ≪≫
      Etale.Big.gammaGlobalSectionsIso V.unop.left)
  apply e.injective
  simp only [map_mul]
  exact @mul_comm (globalSectionsRing V.unop.left) _ (e x) (e y)

/-- The spaces-étale structure sheaf with its sectionwise commutativity retained. -/
private def spacesCommSheaf : Sheaf (spacesEtaleTopology X) CommRingCat.{u} :=
  ⟨SheafOfModules.TensorScalarExtension.commView (spacesStructureSheaf X).obj
    spacesCoefficientComm, by
      apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
      exact (spacesStructureSheaf X).property⟩

/-- Inverse image of the structure sheaf retains multiplicative commutativity. -/
private theorem inverseCoefficientComm (V : (SpacesEtale U)ᵒᵖ)
    (x y : ((spacesEtaleAugmentationRinged U a).toTopos.ringInverseImage.obj
      (spacesRingedSite X).structureSheaf).obj.obj V) : x * y = y * x := by
  let e := Iso.ringCatIsoToRingEquiv
    (((spacesEtaleAugmentationRinged U a).toTopos.commRingInverseImageForgetRingIso.app
      (spacesCommSheaf (X := X))).symm.hom.hom.app V |> asIso)
  apply e.injective
  simp only [map_mul]
  exact @mul_comm
    (((spacesEtaleAugmentationRinged U a).toTopos.commRingInverseImage.obj
      (spacesCommSheaf (X := X))).obj.obj V) _ (e x) (e y)

/-- Sections of the total structure sheaf form commutative rings. -/
private theorem totalCoefficientComm (V : (SpacesEtale U)ᵒᵖ)
    (x y : (etaleTotalStructureSheaf U).obj.obj V) : x * y = y * x :=
  @mul_comm (globalSectionsRing V.unop.obj.left) _ x y

/-- Extension of scalars along the inverse-image structure map uses sectionwise tensors
followed by module sheafification. -/
def structureMapScalarExtension :
    SheafOfModules.{u} ((spacesEtaleAugmentationRinged U a).toTopos.ringInverseImage.obj
      (spacesRingedSite X).structureSheaf) ⥤
      RingedSite.ModuleCat.{u} (etaleTotalRingedSite U) :=
  SheafOfModules.TensorScalarExtension.functor
    (spacesEtaleAugmentationRinged U a).structureMap
    (inverseCoefficientComm a) totalCoefficientComm

/-- Tensor extension along the inverse-image structure map is adjoint to restriction. -/
def structureMapScalarAdjunction :
    structureMapScalarExtension a ⊣
      SheafOfModules.restrictScalars.{u} (spacesEtaleAugmentationRinged U a).structureMap :=
  SheafOfModules.TensorScalarExtension.adjunction
    (spacesEtaleAugmentationRinged U a).structureMap
    (inverseCoefficientComm a) totalCoefficientComm

/-- Restriction of scalars along the inverse-image structure map of the spaces-étale
augmentation is a right adjoint, so module pullback exists. -/
theorem restrictScalars_structureMap_isRightAdjoint :
    (SheafOfModules.restrictScalars.{u}
      (spacesEtaleAugmentationRinged U a).structureMap).IsRightAdjoint :=
  (structureMapScalarAdjunction a).isRightAdjoint

/-- Inverse image `a^*` of modules along the spaces-étale augmentation. -/
abbrev modulePullback :
    RingedSite.ModuleCat.{u} (spacesRingedSite X) ⥤
      RingedSite.ModuleCat.{u} (etaleTotalRingedSite U) :=
  @RingedSite.ToposHom.modulePullback.{u + 1, u + 1, u + 1, u + 1, u}
    _ _ _ _ (spacesEtaleAugmentationRinged U a) (restrictScalars_structureMap_isRightAdjoint a)

/-- Direct image `a_*` of modules along the spaces-étale augmentation. -/
abbrev modulePushforward :
    RingedSite.ModuleCat.{u} (etaleTotalRingedSite U) ⥤
      RingedSite.ModuleCat.{u} (spacesRingedSite X) :=
  (spacesEtaleAugmentationRinged U a).modulePushforward

/-- The adjunction `a^* ⊣ a_*` of modules along the spaces-étale augmentation. -/
abbrev moduleAdjunction : modulePullback a ⊣ modulePushforward a :=
  @RingedSite.ToposHom.moduleAdjunction.{u + 1, u + 1, u + 1, u + 1, u}
    _ _ _ _ (spacesEtaleAugmentationRinged U a) (restrictScalars_structureMap_isRightAdjoint a)

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
