/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction

/-!
# Change of rings for module sheafification

A morphism from a module presheaf to a restricted target presheaf descends canonically to a
morphism from its sheafification to the restriction of the target sheafification.  This is the
common adjunction layer used by sheaf-level base-change constructions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe c v w

namespace SheafOfModules.RingedSite.ModuleSheafification

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O O' : Sheaf J CommRingCat.{w}}
variable (b : O ⟶ O')
variable {P : PresheafOfModules (ringSheaf J O).obj}
variable {Q : PresheafOfModules (ringSheaf J O').obj}

/-- A presheaf morphism into a restricted target descends to the corresponding morphism between
module sheafifications. -/
noncomputable def mapToRestriction
    (f : P ⟶ (PresheafOfModules.restrictScalars (ringSheafMap b).hom).obj Q) :
    (moduleSheafification O).obj P ⟶
      (restrictionAlong b).obj ((moduleSheafification O').obj Q) :=
  ((moduleSheafificationAdjunction O).homEquiv
    P ((restrictionAlong b).obj ((moduleSheafification O').obj Q))).symm
      (f ≫
        (PresheafOfModules.restrictScalars (ringSheafMap b).hom).map
          ((moduleSheafificationUnit O').app Q))

/-- Restrict a module presheaf before sheafifying it over the source ring sheaf. -/
abbrev restrictThenSheafify (b : O ⟶ O') :=
  PresheafOfModules.restrictScalars (ringSheafMap b).hom ⋙ moduleSheafification O

/-- Sheafify a module presheaf over the target ring sheaf and then restrict scalars. -/
abbrev sheafifyThenRestrict (b : O ⟶ O') :=
  moduleSheafification O' ⋙ restrictionAlong b

/-- The canonical adjunction comparison from sheafification after restriction to restriction
after sheafification. -/
noncomputable def restrictionComparison (b : O ⟶ O')
    (Q : PresheafOfModules (ringSheaf J O').obj) :
    (restrictThenSheafify b).obj Q ⟶ (sheafifyThenRestrict b).obj Q :=
  mapToRestriction b (𝟙 _)

/-- The pointwise additive identity intertwines the two scalar actions occurring when restriction
of scalars is exchanged with module sheafification. -/
theorem restrictionAppIso_smul (b : O ⟶ O')
    (Q : PresheafOfModules (ringSheaf J O').obj) (X : Cᵒᵖ)
    (r : (ringSheaf J O).obj.obj X) :
    (Iso.refl _).hom ≫ (((sheafifyThenRestrict b).obj Q).val.obj X).smul r =
      (((restrictThenSheafify b).obj Q).val.obj X).smul r ≫ (Iso.refl _).hom := sorry

/-- The pointwise identity isomorphism between the two orders of restriction and
sheafification. -/
noncomputable def restrictionAppIso (b : O ⟶ O')
    (Q : PresheafOfModules (ringSheaf J O').obj) (X : Cᵒᵖ) :
    ((restrictThenSheafify b).obj Q).val.obj X ≅
      ((sheafifyThenRestrict b).obj Q).val.obj X :=
  ModuleCat.isoMk (Iso.refl _) (restrictionAppIso_smul b Q X)

/-- The pointwise restriction-sheafification isomorphisms commute with restriction maps. -/
theorem restrictionAppIso_naturality (b : O ⟶ O')
    (Q : PresheafOfModules (ringSheaf J O').obj) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((restrictThenSheafify b).obj Q).val.map f ≫
        (ModuleCat.restrictScalars (((ringSheaf J O).obj.map f).hom)).map
          (restrictionAppIso b Q Y).hom =
      (restrictionAppIso b Q X).hom ≫ ((sheafifyThenRestrict b).obj Q).val.map f := sorry

/-- The presheaves underlying the two orders of restriction and sheafification are canonically
isomorphic. -/
noncomputable def restrictionPresheafIso (b : O ⟶ O')
    (Q : PresheafOfModules (ringSheaf J O').obj) :
    ((restrictThenSheafify b).obj Q).val ≅ ((sheafifyThenRestrict b).obj Q).val :=
  PresheafOfModules.isoMk (restrictionAppIso b Q)
    (fun _ _ f ↦ restrictionAppIso_naturality b Q f)

/-- Restriction of scalars commutes with module sheafification on each module presheaf. -/
@[stacks 0G3Y "restriction-sheafification component isomorphism"]
noncomputable def restrictionComponentIso (b : O ⟶ O')
    (Q : PresheafOfModules (ringSheaf J O').obj) :
    (restrictThenSheafify b).obj Q ≅ (sheafifyThenRestrict b).obj Q :=
  (SheafOfModules.fullyFaithfulForget (ringSheaf J O)).preimageIso
    (restrictionPresheafIso b Q)

/-- The restriction-sheafification comparison is natural in the module presheaf. -/
@[stacks 0G3Y "restriction-sheafification comparison naturality"]
theorem restrictionComponentIso_naturality (b : O ⟶ O')
    {P Q : PresheafOfModules (ringSheaf J O').obj} (f : P ⟶ Q) :
      (restrictThenSheafify b).map f ≫ (restrictionComponentIso b Q).hom =
      (restrictionComponentIso b P).hom ≫ (sheafifyThenRestrict b).map f := sorry

/-- The inverse restriction-sheafification comparison is natural in the module presheaf. -/
@[stacks 0G3Y "inverse restriction-sheafification comparison naturality"]
theorem restrictionComponentIso_inv_naturality (b : O ⟶ O')
    {P Q : PresheafOfModules (ringSheaf J O').obj} (f : P ⟶ Q) :
    (sheafifyThenRestrict b).map f ≫ (restrictionComponentIso b Q).inv =
      (restrictionComponentIso b P).inv ≫ (restrictThenSheafify b).map f := sorry

/-- The forward restriction-sheafification comparisons form a natural transformation. -/
@[stacks 0G3Y "restriction-sheafification forward natural transformation"]
noncomputable def restrictionNatTrans (b : O ⟶ O') :
    restrictThenSheafify b ⟶ sheafifyThenRestrict b where
  app Q := (restrictionComponentIso b Q).hom
  naturality _ _ f := restrictionComponentIso_naturality b f

/-- The inverse restriction-sheafification comparisons form a natural transformation. -/
@[stacks 0G3Y "restriction-sheafification inverse natural transformation"]
noncomputable def restrictionInvNatTrans (b : O ⟶ O') :
    sheafifyThenRestrict b ⟶ restrictThenSheafify b where
  app Q := (restrictionComponentIso b Q).inv
  naturality _ _ f := restrictionComponentIso_inv_naturality b f

/-- A component of the forward restriction-sheafification comparison is the forward
component isomorphism. -/
@[simp, stacks 0G3Y "restriction-sheafification forward natural transformation component"]
theorem restrictionNatTrans_app (b : O ⟶ O')
    (Q : PresheafOfModules (ringSheaf J O').obj) :
    (restrictionNatTrans b).app Q = (restrictionComponentIso b Q).hom := sorry

/-- A component of the inverse restriction-sheafification comparison is the inverse
component isomorphism. -/
@[simp, stacks 0G3Y "restriction-sheafification inverse natural transformation component"]
theorem restrictionInvNatTrans_app (b : O ⟶ O')
    (Q : PresheafOfModules (ringSheaf J O').obj) :
    (restrictionInvNatTrans b).app Q = (restrictionComponentIso b Q).inv := sorry

/-- The forward restriction-sheafification natural transformation followed by its inverse
is the identity. -/
@[simp, stacks 0G3Y "restriction-sheafification forward-inverse law"]
theorem restrictionNatTrans_hom_inv_id (b : O ⟶ O') :
    restrictionNatTrans b ≫ restrictionInvNatTrans b = 𝟙 _ := sorry

/-- The inverse restriction-sheafification natural transformation followed by its forward
map is the identity. -/
@[simp, stacks 0G3Y "restriction-sheafification inverse-forward law"]
theorem restrictionNatTrans_inv_hom_id (b : O ⟶ O') :
    restrictionInvNatTrans b ≫ restrictionNatTrans b = 𝟙 _ := sorry

/-- Restriction of scalars and module sheafification commute by a canonical natural
isomorphism. -/
@[stacks 0G3Y "restriction and module sheafification natural isomorphism"]
noncomputable def restrictionIso (b : O ⟶ O') :
    restrictThenSheafify b ≅ sheafifyThenRestrict b where
  hom := restrictionNatTrans b
  inv := restrictionInvNatTrans b
  hom_inv_id := restrictionNatTrans_hom_inv_id b
  inv_hom_id := restrictionNatTrans_inv_hom_id b

/-- The forward map of `restrictionIso` is the explicit restriction-sheafification natural
transformation. -/
@[simp, stacks 0G3Y "restriction-sheafification natural isomorphism hom"]
theorem restrictionIso_hom (b : O ⟶ O') :
    (restrictionIso b).hom = restrictionNatTrans b := sorry

/-- The inverse map of `restrictionIso` is the explicit inverse restriction-sheafification
natural transformation. -/
@[simp, stacks 0G3Y "restriction-sheafification natural isomorphism inverse"]
theorem restrictionIso_inv (b : O ⟶ O') :
    (restrictionIso b).inv = restrictionInvNatTrans b := sorry

/-- A component of `restrictionIso` is the objectwise restriction-sheafification
isomorphism. -/
@[simp, stacks 0G3Y "restriction-sheafification natural isomorphism component"]
theorem restrictionIso_app (b : O ⟶ O')
    (Q : PresheafOfModules (ringSheaf J O').obj) :
    (restrictionIso b).app Q = restrictionComponentIso b Q := sorry

/-- An inverse component of `restrictionIso` is the explicit objectwise inverse comparison. -/
@[simp, stacks 0G3Y "restriction-sheafification natural isomorphism inverse component"]
theorem restrictionIso_inv_app (b : O ⟶ O')
    (Q : PresheafOfModules (ringSheaf J O').obj) :
    (restrictionIso b).inv.app Q = (restrictionComponentIso b Q).inv := sorry

/-- Sheafify a morphism which is linear only after restricting scalars, while retaining the
target-ring module sheaves at both endpoints. -/
noncomputable def mapAfterRestriction (b : O ⟶ O')
    {P Q : PresheafOfModules (ringSheaf J O').obj}
    (f : (PresheafOfModules.restrictScalars (ringSheafMap b).hom).obj P ⟶
      (PresheafOfModules.restrictScalars (ringSheafMap b).hom).obj Q) :
    (restrictionAlong b).obj ((moduleSheafification O').obj P) ⟶
      (restrictionAlong b).obj ((moduleSheafification O').obj Q) :=
  (restrictionIso b).inv.app P ≫ (moduleSheafification O).map f ≫
    (restrictionIso b).hom.app Q

section AdjunctionSpec

variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Under the module-sheafification adjunction, `mapToRestriction` is represented by the
original presheaf morphism followed by the restricted target sheafification unit. -/
theorem homEquiv_mapToRestriction
    (f : P ⟶ (PresheafOfModules.restrictScalars (ringSheafMap b).hom).obj Q) :
    (moduleSheafificationAdjunction O).homEquiv P
        ((restrictionAlong b).obj ((moduleSheafification O').obj Q))
        (mapToRestriction b f) =
      f ≫
        (PresheafOfModules.restrictScalars (ringSheafMap b).hom).map
          ((moduleSheafificationUnit O').app Q) := sorry

/-- The hom component of the restriction-sheafification isomorphism is the canonical adjunction
comparison. -/
@[simp, stacks 0G3Y "restriction-sheafification natural isomorphism hom component"]
theorem restrictionIso_hom_app
    (Q : PresheafOfModules (ringSheaf J O').obj) :
    (restrictionIso b).hom.app Q = restrictionComparison b Q := sorry

end AdjunctionSpec

end SheafOfModules.RingedSite.ModuleSheafification
