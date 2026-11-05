/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Balanced
public import ReasLib.CategoryTheory.Functor.OfSequence.Colimit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealProduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Noetherian

/-!
# Ideal-power Hom colimits and restriction on algebraic spaces

The open complement of a quasi-coherent ideal and the resulting comparison
between ideal-power Hom colimits and morphisms on that complement.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

/-- Module sheaves on the small étale site of an algebraic space form a balanced category. -/
instance balanced_modules {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Balanced X.Modules :=
  sorry

/-- The open complement of the closed subspace cut out by a quasi-coherent ideal sheaf. -/
noncomputable abbrev idealOpenComplement {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] : AlgebraicSpace S :=
  closedImmersionComplement (subschemeι I)

/-- The open immersion of the complement of the closed subspace cut out by an ideal. -/
noncomputable abbrev idealOpenComplementι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    idealOpenComplement I ⟶ X :=
  closedImmersionComplementι (subschemeι I)

/-- The first ideal-power product recovers the ordinary product subobject. -/
theorem idealPowerProductSubobject_one {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (F : X.Modules) :
    idealPowerProductSubobject I F 1 = idealProductSubobject I F :=
  sorry

/-- The first ideal-power product is characterized by its local product sections. -/
theorem idealPowerProductSubobject_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (F : X.Modules) (G : Subobject F) :
    idealPowerProductSubobject I F 1 ≤ G ↔
      SheafOfModules.Subobject.containsSections G
        (idealProductSite I F) (idealProductSection I F) :=
  sorry

namespace IdealPowerProduct

/-- Multiplication by successive ideal powers defines a descending filtration. -/
theorem antitone {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (F : X.Modules) (n : ℕ) :
    idealPowerProductSubobject I F (n + 1) ≤ idealPowerProductSubobject I F n :=
  sorry

end IdealPowerProduct

/-- The restricted inclusion of an ideal-power product is a monomorphism. -/
instance idealPowerProductSubobject_restrictArrow_mono {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (F : X.Modules) (n : ℕ) :
    Mono
      ((restrictFunctor (idealOpenComplementι I)).map
        (idealPowerProductSubobject I F n).arrow) :=
  sorry

/-- The restricted inclusion of an ideal-power product is an epimorphism. -/
instance idealPowerProductSubobject_restrictArrow_epi {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (F : X.Modules) (n : ℕ) :
    Epi
      ((restrictFunctor (idealOpenComplementι I)).map
        (idealPowerProductSubobject I F n).arrow) :=
  sorry

/-- The ideal-power inclusion becomes an isomorphism on the open complement. -/
noncomputable instance idealPowerProductSubobject_restrictArrow_isIso {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (F : X.Modules) (n : ℕ) :
    IsIso
      ((restrictFunctor (idealOpenComplementι I)).map
        (idealPowerProductSubobject I F n).arrow) :=
  isIso_of_mono_of_epi
    ((restrictFunctor (idealOpenComplementι I)).map
      (idealPowerProductSubobject I F n).arrow)

end Modules

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The additive group of module morphisms from an ideal-power product to a module. -/
noncomputable def idealPowerProductHomStage
    (I : IdealSubobject X) (G F : X.Modules) (n : ℕ) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of ((idealPowerProductSubobject I G n : X.Modules) ⟶ F)

/-- Precomposition with the successive ideal-power inclusion gives the transition map. -/
noncomputable def idealPowerProductHomTransition {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (G F : X.Modules) (n : ℕ) :
    idealPowerProductHomStage I G F n ⟶
      idealPowerProductHomStage I G F (n + 1) :=
  AddCommGrpCat.ofHom
    (Preadditive.leftComp F
      (Subobject.ofLE
        (idealPowerProductSubobject I G (n + 1))
        (idealPowerProductSubobject I G n)
        (IdealPowerProduct.antitone I G n)))

/-- The sequential additive-group diagram of ideal-power Hom stages. -/
noncomputable def idealPowerProductHomDiagram {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (G F : X.Modules) : ℕ ⥤ AddCommGrpCat.{u + 1} :=
  Functor.ofSequence (idealPowerProductHomTransition I G F)

/-- The restricted structure module is identified with the structure module of the source.
Both maps are the identity on sections, since `restrictStructureMap` is the identity
on each chart. -/
noncomputable def restrictFunctorObjUnitIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] :
    (restrictFunctor f).obj (SheafOfModules.unit (structureSheaf Y)) ≅
      SheafOfModules.unit (structureSheaf X) where
  hom :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := ((restrictFunctor f).obj
              (SheafOfModules.unit (structureSheaf Y))).val.obj U)
            (Y := (SheafOfModules.unit (structureSheaf X)).val.obj U)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          naturality := fun _ ↦ by ext <;> rfl } }
  inv := SheafOfModules.unitToPushforwardObjUnit (restrictStructureMap f)
  hom_inv_id := by ext U <;> rfl
  inv_hom_id := by ext U <;> rfl

/-- Restriction of the structure module along an étale morphism is a monomorphism. -/
instance restrictFunctorObjUnit_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] :
    Mono (SheafOfModules.unitToPushforwardObjUnit (restrictStructureMap f)) :=
  by
    letI : IsIso (SheafOfModules.unitToPushforwardObjUnit (restrictStructureMap f)) :=
      (restrictFunctorObjUnitIso f).isIso_inv
    infer_instance

/-- Restriction of the structure module along an étale morphism is an epimorphism. -/
instance restrictFunctorObjUnit_epi {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] :
    Epi (SheafOfModules.unitToPushforwardObjUnit (restrictStructureMap f)) :=
  by
    letI : IsIso (SheafOfModules.unitToPushforwardObjUnit (restrictStructureMap f)) :=
      (restrictFunctorObjUnitIso f).isIso_inv
    infer_instance

/-- The structure-module comparison under an étale restriction is an isomorphism. -/
noncomputable instance restrictFunctorObjUnit_isIso {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (restrictStructureMap f)) :=
  (restrictFunctorObjUnitIso f).isIso_inv

/-- A stage Hom morphism restricts to a morphism on the ideal complement. -/
noncomputable def idealPowerProductHomToRestrictionStageMap {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (G F : X.Modules) (n : ℕ) :
    idealPowerProductHomStage I G F n ⟶
      AddCommGrpCat.of
        ((restrictFunctor (idealOpenComplementι I)).obj G ⟶
          (restrictFunctor (idealOpenComplementι I)).obj F) :=
  AddCommGrpCat.ofHom
    { toFun := fun φ ↦
        inv ((restrictFunctor (idealOpenComplementι I)).map
            (idealPowerProductSubobject I G n).arrow) ≫
          (restrictFunctor (idealOpenComplementι I)).map φ
      map_zero' := sorry
      map_add' := sorry }

/-- Restriction to the complement is compatible with the successor transition. -/
theorem idealPowerProductHomToRestrictionStageMap_naturality {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (G F : X.Modules) (n : ℕ) :
    idealPowerProductHomTransition I G F n ≫
        idealPowerProductHomToRestrictionStageMap I G F (n + 1) =
      idealPowerProductHomToRestrictionStageMap I G F n :=
  sorry

/-- The canonical comparison from the ideal-power Hom colimit to restricted Hom. -/
noncomputable def idealPowerProductHomColimitToRestriction {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (G F : X.Modules) :
    colimit (idealPowerProductHomDiagram I G F) ⟶
      AddCommGrpCat.of
        ((restrictFunctor (idealOpenComplementι I)).obj G ⟶
          (restrictFunctor (idealOpenComplementι I)).obj F) :=
  Functor.ofSequence.colimitDesc
    (idealPowerProductHomTransition I G F)
    (idealPowerProductHomToRestrictionStageMap I G F)
    (idealPowerProductHomToRestrictionStageMap_naturality I G F)

/-- The colimit comparison restricts to its defining stage map. -/
@[reassoc]
theorem idealPowerProductHomColimitToRestriction_ι {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (G F : X.Modules) (n : ℕ) :
    colimit.ι (idealPowerProductHomDiagram I G F) n ≫
        idealPowerProductHomColimitToRestriction I G F =
      idealPowerProductHomToRestrictionStageMap I G F n :=
  sorry

/-- For coherent `G` and quasi-coherent `F` on a Noetherian space, the comparison is an isomorphism. -/
noncomputable instance idealPowerProductHomColimitToRestriction_isIso {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (G F : X.Modules) [G.IsCoherent] [F.IsQuasicoherent] :
    IsIso (idealPowerProductHomColimitToRestriction I G F) :=
  sorry

/-- The ideal-sheaf specialization of the ideal-power Hom diagram. -/
noncomputable abbrev idealSheafPowerHomDiagram {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (F : X.Modules) : ℕ ⥤ AddCommGrpCat.{u + 1} :=
  idealPowerProductHomDiagram I (SheafOfModules.unit (structureSheaf X)) F

/-- The ideal-power Hom comparison specialized to sections on the complement. -/
noncomputable def idealSheafPowerHomColimitToComplementSections {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (F : X.Modules) :
    colimit (idealSheafPowerHomDiagram I F) ⟶
      AddCommGrpCat.of
        (SheafOfModules.unit (structureSheaf (idealOpenComplement I)) ⟶
          (restrictFunctor (idealOpenComplementι I)).obj F) :=
  idealPowerProductHomColimitToRestriction I
      (SheafOfModules.unit (structureSheaf X)) F ≫
    AddCommGrpCat.ofHom
      (Preadditive.leftComp ((restrictFunctor (idealOpenComplementι I)).obj F)
        (SheafOfModules.unitToPushforwardObjUnit
          (restrictStructureMap (idealOpenComplementι I))))

/-- On a Noetherian algebraic space, the specialized comparison is an isomorphism. -/
noncomputable instance idealSheafPowerHomColimitToComplementSections_isIso
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] (F : X.Modules)
    [F.IsQuasicoherent] :
    IsIso (idealSheafPowerHomColimitToComplementSections I F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
