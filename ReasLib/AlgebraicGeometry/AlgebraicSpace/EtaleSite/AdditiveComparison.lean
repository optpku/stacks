module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AdditiveForget
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing

/-!
# Additive comparisons on the étale sites of algebraic spaces

Explicit comparisons identify the additive sheaves underlying module direct images
and compare inverse images on the small and spaces étale sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace.Thickening
open Sheaf.InternalModule RingedSite.ToposHom
noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}}

/-- Forget ring-valued sheaves on the spaces-étale site to abelian groups. -/
abbrev forgetSpacesRing (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) RingCat.{u} ⥤
      Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u} :=
  sheafCompose (spacesEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})

/-- `forgetSpacesRing X` is sheaf composition with `forget₂ RingCat AddCommGrpCat`. -/
theorem forgetSpacesRing_eq (X : AlgebraicSpace S) :
    forgetSpacesRing X =
      sheafCompose (spacesEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u}) :=
  rfl

/-- The underlying type-valued sheaf of an `𝒪_X`-module agrees with forgetting the
additive sheaf `toSheaf`. -/
def toSheafUnderlyingIso (X : AlgebraicSpace S) (F : X.Modules) :
    (EtaleAdditive.ForgetComparison.forgetAdd X).obj ((SheafOfModules.toSheaf (structureSheaf X)).obj F) ≅
      (ToInternal.underlying (structureSheaf X)).obj F where
  hom := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  inv := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `toSheafUnderlyingIso` is the identity on every section type. -/
theorem toSheafUnderlyingIso_hom_eq (X : AlgebraicSpace S) (F : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (toSheafUnderlyingIso X F).hom.hom.app U = 𝟙 _ :=
  rfl

/-- Named comparison from the underlying sheaf of `a_* F` to the geometric direct image
of the underlying sheaf of `F`. -/
def modulePushforwardForgetHom {X Y : AlgebraicSpace S} (a : X ⟶ Y) (F : X.Modules) :
    (ToInternal.underlying (structureSheaf Y)).obj ((Modules.pushforward a).obj F) ⟶
      (typePushforward a).obj ((ToInternal.underlying (structureSheaf X)).obj F) :=
  (ModulePushforward.forgetIso (ringedToposHom a)).hom.app F

/-- The underlying module direct-image comparison is the component of the canonical forgetful isomorphism. -/
theorem modulePushforwardForgetHom_eq {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : X.Modules) :
    modulePushforwardForgetHom a F =
      (ModulePushforward.forgetIso (ringedToposHom a)).hom.app F :=
  rfl

/-- Additivity of a specified map between underlying type-valued sheaves. -/
def typeHomIsAdditive {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}}
    (f : (EtaleAdditive.ForgetComparison.forgetAdd X).obj F ⟶ (EtaleAdditive.ForgetComparison.forgetAdd X).obj G) : Prop :=
  ∀ U (x y : F.obj.obj U), ConcreteCategory.hom (f.hom.app U) (x + y) =
    @Add.add (G.obj.obj U) inferInstance
      (ConcreteCategory.hom (f.hom.app U) x) (ConcreteCategory.hom (f.hom.app U) y)

/-- The specified module direct-image comparison preserves addition sectionwise. -/
theorem modulePushforwardForgetAdd_add {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : X.Modules) :
    typeHomIsAdditive ((toSheafUnderlyingIso Y ((Modules.pushforward a).obj F)).hom ≫
      modulePushforwardForgetHom a F ≫
      (typePushforward a).map (toSheafUnderlyingIso X F).inv ≫
      (EtaleAdditive.directImageForgetIso a).inv.app
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F)) := sorry

/-- Named additive comparison `toSheaf (a_* F) ⟶ a_* (toSheaf F)`, obtained from
`ModulePushforward.forgetIso` rather than a propositional sheaf equality. -/
def modulePushforwardForgetAdd {X Y : AlgebraicSpace S} (a : X ⟶ Y) (F : X.Modules) :
    (SheafOfModules.toSheaf (structureSheaf Y)).obj ((Modules.pushforward a).obj F) ⟶
      (EtaleAdditive.directImage a).obj ((SheafOfModules.toSheaf (structureSheaf X)).obj F) :=
  EtaleAdditive.ForgetComparison.homOfUnderlying (hadd := modulePushforwardForgetAdd_add a F)
    ((toSheafUnderlyingIso Y ((Modules.pushforward a).obj F)).hom ≫
      modulePushforwardForgetHom a F ≫
      (typePushforward a).map (toSheafUnderlyingIso X F).inv ≫
      (EtaleAdditive.directImageForgetIso a).inv.app
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F))

/-- The additive direct-image comparison is the lift of its specified underlying sheaf map. -/
theorem modulePushforwardForgetAdd_eq {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : X.Modules) :
    modulePushforwardForgetAdd a F =
      EtaleAdditive.ForgetComparison.homOfUnderlying (hadd := modulePushforwardForgetAdd_add a F)
        ((toSheafUnderlyingIso Y ((Modules.pushforward a).obj F)).hom ≫
          modulePushforwardForgetHom a F ≫
          (typePushforward a).map (toSheafUnderlyingIso X F).inv ≫
          (EtaleAdditive.directImageForgetIso a).inv.app
            ((SheafOfModules.toSheaf (structureSheaf X)).obj F)) :=
  rfl

/-- The unit `𝒪`-module and the underlying additive structure sheaf agree. -/
def unitToForgetAddIso (X : AlgebraicSpace S) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj
        (SheafOfModules.unit (structureSheaf X)) ≅
      (sheafCompose (smallEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf X) where
  hom := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  inv := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `unitToForgetAddIso` is the identity on every additive section group. -/
theorem unitToForgetAddIso_hom_eq (X : AlgebraicSpace S) (U : (smallEtaleSite X)ᵒᵖ) :
    (unitToForgetAddIso X).hom.hom.app U = 𝟙 _ :=
  rfl

/-- The specified module direct-image comparison preserves addition sectionwise. -/
theorem modulePushforwardForgetAddInv_add {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : X.Modules) :
    typeHomIsAdditive ((EtaleAdditive.directImageForgetIso a).hom.app
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F) ≫
      (typePushforward a).map (toSheafUnderlyingIso X F).hom ≫
      (ModulePushforward.forgetIso (ringedToposHom a)).inv.app F ≫
      (toSheafUnderlyingIso Y ((Modules.pushforward a).obj F)).inv) := sorry

/-- Named additive comparison `i_* (toSheaf F) ⟶ toSheaf (i_* F)`, inverse to
`modulePushforwardForgetAdd`. -/
def modulePushforwardForgetAddInv {X Y : AlgebraicSpace S} (a : X ⟶ Y) (F : X.Modules) :
    (EtaleAdditive.directImage a).obj ((SheafOfModules.toSheaf (structureSheaf X)).obj F) ⟶
      (SheafOfModules.toSheaf (structureSheaf Y)).obj ((Modules.pushforward a).obj F) :=
  EtaleAdditive.ForgetComparison.homOfUnderlying (hadd := modulePushforwardForgetAddInv_add a F)
    ((EtaleAdditive.directImageForgetIso a).hom.app
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F) ≫
      (typePushforward a).map (toSheafUnderlyingIso X F).hom ≫
      (ModulePushforward.forgetIso (ringedToposHom a)).inv.app F ≫
      (toSheafUnderlyingIso Y ((Modules.pushforward a).obj F)).inv)

/-- The reverse additive direct-image comparison lifts the inverse underlying sheaf comparison. -/
theorem modulePushforwardForgetAddInv_eq {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : X.Modules) :
    modulePushforwardForgetAddInv a F =
      EtaleAdditive.ForgetComparison.homOfUnderlying (hadd := modulePushforwardForgetAddInv_add a F)
        ((EtaleAdditive.directImageForgetIso a).hom.app
            ((SheafOfModules.toSheaf (structureSheaf X)).obj F) ≫
          (typePushforward a).map (toSheafUnderlyingIso X F).hom ≫
          (ModulePushforward.forgetIso (ringedToposHom a)).inv.app F ≫
          (toSheafUnderlyingIso Y ((Modules.pushforward a).obj F)).inv) :=
  rfl

/-- Type-valued restriction from spaces to the dense small étale subsite. -/
abbrev restrictSpacesType (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) (Type u) ⥤ Sheaf (smallEtaleTopology X) (Type u) :=
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces X).sheafPushforwardContinuous (Type u)
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Direct-image comparison induced by the actual base-change square of site functors. -/
def smallSpacesPushforwardIso {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    (morphismOfTopoi a).pushforward ≅
      (EtaleTopos.siteEquivalence X).inverse ⋙
        (spacesRingedToposHom a).toTopos.pushforward ⋙
          (EtaleTopos.siteEquivalence Y).functor :=
  Functor.isoWhiskerLeft (EtaleTopos.siteEquivalence X).inverse
    (Functor.sheafPushforwardContinuousComp'
      (smallEtaleInclusion_comp_spacesEtalePullback a) (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X)).symm

/-- The inverse-image mate of the specified direct-image comparison. -/
def smallSpacesInverseIso {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    (EtaleTopos.siteEquivalence Y).inverse ⋙
        (spacesRingedToposHom a).toTopos.inverseImage ⋙
          (EtaleTopos.siteEquivalence X).functor ≅ (morphismOfTopoi a).inverseImage :=
  Adjunction.leftAdjointUniq
    ((((EtaleTopos.siteEquivalence Y).symm.toAdjunction.comp
      (spacesRingedToposHom a).toTopos.adjunction).comp
        (EtaleTopos.siteEquivalence X).toAdjunction).ofNatIsoRight
          (smallSpacesPushforwardIso a).symm)
    (morphismOfTopoi a).adjunction

/-- Inverse image commutes with the underlying type of an additive sheaf:
the map is the adjunction mate of the additive unit and the direct-image comparison. -/
def inverseImageForgetAddHom {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    (morphismOfTopoi a).inverseImage.obj ((EtaleAdditive.ForgetComparison.forgetAdd Y).obj F) ⟶
      (EtaleAdditive.ForgetComparison.forgetAdd X).obj ((EtaleAdditive.inverseImage a).obj F) :=
  ((morphismOfTopoi a).adjunction.homEquiv _ _).symm
    ((EtaleAdditive.ForgetComparison.forgetAdd Y).map ((EtaleAdditive.adjunction a).unit.app F) ≫
      (EtaleAdditive.directImageForgetIso a).hom.app ((EtaleAdditive.inverseImage a).obj F))

/-- The canonical additive forgetful mate is invertible by its constructed inverse. -/
instance inverseImageForgetAddHom_isIso {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    IsIso (inverseImageForgetAddHom a F) := by
  exact (congrArg (fun f ↦ IsIso f)
    (EtaleAdditive.ForgetComparison.underlyingIso_hom_mate a F)).mp
      ((EtaleAdditive.ForgetComparison.underlyingIso a).app F).isIso_hom

/-- The inverse is the underlying reverse adjunction-comparison map. -/
def inverseImageForgetAddInv {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    (EtaleAdditive.ForgetComparison.forgetAdd X).obj ((EtaleAdditive.inverseImage a).obj F) ⟶
      (morphismOfTopoi a).inverseImage.obj ((EtaleAdditive.ForgetComparison.forgetAdd Y).obj F) :=
  ((EtaleAdditive.ForgetComparison.underlyingIso a).app F).inv

/-- The original forward mate followed by its constructed inverse is the identity. -/
theorem inverseImageForgetAdd_hom_inv_id {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    inverseImageForgetAddHom a F ≫ inverseImageForgetAddInv a F = 𝟙 _ := by
  exact (congrArg (fun f ↦ f ≫ inverseImageForgetAddInv a F)
    (EtaleAdditive.ForgetComparison.underlyingIso_hom_mate a F)).symm.trans
      ((EtaleAdditive.ForgetComparison.underlyingIso a).app F).hom_inv_id

/-- The constructed inverse followed by the original forward mate is the identity. -/
theorem inverseImageForgetAdd_inv_hom_id {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    inverseImageForgetAddInv a F ≫ inverseImageForgetAddHom a F = 𝟙 _ := by
  exact (congrArg (fun f ↦ inverseImageForgetAddInv a F ≫ f)
    (EtaleAdditive.ForgetComparison.underlyingIso_hom_mate a F)).symm.trans
      ((EtaleAdditive.ForgetComparison.underlyingIso a).app F).inv_hom_id

/-- The underlying comparison for the inverse image of the structure sheaf,
composed from ring forgetting, dense-subsite Kan extension, and adjunction mates. -/
def restrictInverseImageTypeHom {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    (EtaleAdditive.ForgetComparison.forgetAdd X).obj ((EtaleAdditive.restriction X).obj
      ((forgetSpacesRing X).obj ((spacesRingedToposHom a).toTopos.ringInverseImage.obj
        (spacesStructureSheaf Y)))) ⟶
    (EtaleAdditive.ForgetComparison.forgetAdd X).obj ((EtaleAdditive.inverseImage a).obj
      ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y))) :=
  (restrictSpacesType X).map
      ((spacesRingedToposHom a).toTopos.ringInverseImageForgetIso.hom.app
        (spacesStructureSheaf Y)) ≫
    (restrictSpacesType X).map ((spacesRingedToposHom a).toTopos.inverseImage.map
      ((EtaleAdditive.ringExtensionForgetIso Y).hom.app (structureSheaf Y))) ≫
    (smallSpacesInverseIso a).hom.app
      ((sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj (structureSheaf Y)) ≫
    inverseImageForgetAddHom a
      ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y))

/-- The reverse structure-sheaf comparison composes the existing inverse factors in reverse order. -/
def restrictInverseImageTypeInv {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    (EtaleAdditive.ForgetComparison.forgetAdd X).obj ((EtaleAdditive.inverseImage a).obj
      ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y))) ⟶
    (EtaleAdditive.ForgetComparison.forgetAdd X).obj ((EtaleAdditive.restriction X).obj
      ((forgetSpacesRing X).obj ((spacesRingedToposHom a).toTopos.ringInverseImage.obj
        (spacesStructureSheaf Y)))) :=
  inverseImageForgetAddInv a
      ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y)) ≫
    (smallSpacesInverseIso a).inv.app
      ((sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj (structureSheaf Y)) ≫
    (restrictSpacesType X).map ((spacesRingedToposHom a).toTopos.inverseImage.map
      ((EtaleAdditive.ringExtensionForgetIso Y).inv.app (structureSheaf Y))) ≫
    (restrictSpacesType X).map
      ((spacesRingedToposHom a).toTopos.ringInverseImageForgetIso.inv.app
        (spacesStructureSheaf Y))

/-- The specified reverse factors undo the original forward structure comparison. -/
theorem restrictInverseImageTypeHom_inv {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    restrictInverseImageTypeHom a ≫ restrictInverseImageTypeInv a = 𝟙 _ := sorry

/-- The original forward factors undo the specified reverse structure comparison. -/
theorem restrictInverseImageTypeInv_hom {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    restrictInverseImageTypeInv a ≫ restrictInverseImageTypeHom a = 𝟙 _ := sorry

/-- Each factor in the structure-sheaf inverse-image comparison is invertible. -/
instance restrictInverseImageTypeHom_isIso {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    IsIso (restrictInverseImageTypeHom a) :=
  ⟨⟨restrictInverseImageTypeInv a, restrictInverseImageTypeHom_inv a,
    restrictInverseImageTypeInv_hom a⟩⟩

/-- The small-versus-spaces comparison, with underlying maps fixed by adjunction mates. -/
def restrictInverseImageIso {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    (EtaleAdditive.restriction X).obj
        ((forgetSpacesRing X).obj
          ((spacesRingedToposHom a).toTopos.ringInverseImage.obj
            (spacesStructureSheaf Y))) ≅
      (EtaleAdditive.inverseImage a).obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
          (structureSheaf Y)) where
  hom := EtaleAdditive.ForgetComparison.homOfUnderlying (restrictInverseImageTypeHom a) (hadd := sorry)
  inv := EtaleAdditive.ForgetComparison.homOfUnderlying (restrictInverseImageTypeInv a) (hadd := sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
