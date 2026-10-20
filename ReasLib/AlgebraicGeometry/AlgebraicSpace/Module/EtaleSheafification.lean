module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.CommRing
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Étale restriction and module sheafification

Restriction along an étale morphism commutes with sheafification of module presheaves.
The inverse comparison is constructed using the restriction adjunction and sections
on all scheme charts of the geometric fibres.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalModule
open scoped AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Sheafification unit of an `𝒪_Y`-module presheaf, pushed forward along étale restriction. -/
def restrictSheafificationUnit {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    (PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P ⟶
      (SheafOfModules.forget _).obj
        ((restrictFunctor h).obj
          ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj P)) :=
  (PresheafOfModules.pushforward (restrictStructureMap h).hom).map
    ((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (structureSheaf X).obj)).unit.app P)

/-- Compatibility `sheafify(P|_{U_étale}) ⟶ (sheafify P)|_{U_étale}` as the unit/counit
composite `sheafify.map unit ≫ counit`. -/
def restrictSheafificationHom {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
        ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P) ⟶
      (restrictFunctor h).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj P) :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).map
      (restrictSheafificationUnit h P) ≫
    (PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (structureSheaf U).obj)).counit.app
      ((restrictFunctor h).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj P))

/-- Restrict a presheaf section to a chart of the geometric fibre, then apply
the actual sheafification unit on `U`. -/
private def restrictSheafificationPushforwardConeπ {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (V : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange h).obj V)) (smallEtaleToSpaces U).op) :
    (P.obj (op V) : Type u) ⟶
      ((ToInternal.underlying (structureSheaf U)).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
          ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P))).obj.obj a.right :=
  let N := (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
    ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P)
  let η := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 (structureSheaf U).obj)).unit.app
      ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P)
  ↾fun x ↦ (ToInternal.sectionEquiv (structureSheaf U) N a.right).symm
    ((η.app a.right).hom
      ((P.map (op (restrictPostcomposeHomOfSquare h (etaleSquareOfArrow h V a)))).hom x))

/-- The chartwise sheafification sections form a compatible family. -/
private theorem restrictSheafificationPushforwardCone_naturality {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (V : smallEtaleSite X)
    {a b : StructuredArrow (op ((etaleBaseChange h).obj V)) (smallEtaleToSpaces U).op}
    (k : a ⟶ b) :
    𝟙 _ ≫ restrictSheafificationPushforwardConeπ h P V b =
      restrictSheafificationPushforwardConeπ h P V a ≫ ((StructuredArrow.proj (op ((etaleBaseChange h).obj V)) (smallEtaleToSpaces U).op ⋙
      ((ToInternal.underlying (structureSheaf U)).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
          ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P))).obj)).map k :=
  sorry

/-- The cone uses all actual scheme charts over the fibre `U ×_X V`. -/
private def restrictSheafificationPushforwardCone {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (V : smallEtaleSite X) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange h).obj V)) (smallEtaleToSpaces U).op ⋙
      ((ToInternal.underlying (structureSheaf U)).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
          ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P))).obj) where
  pt := (P.obj (op V) : Type u)
  π := { app := restrictSheafificationPushforwardConeπ h P V, naturality := fun {_ _} a ↦ restrictSheafificationPushforwardCone_naturality h P V a }

/-- The universal section lift respects addition. -/
private theorem restrictSheafificationToPushforwardApp_add {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (V : (smallEtaleSite X)ᵒᵖ) :
  let N := (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
    ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P)
  let lift := EtaleTopos.allChartLift U
    ((ToInternal.underlying (structureSheaf U)).obj N) ((etaleBaseChange h).obj V.unop)
    (restrictSheafificationPushforwardCone h P V.unop)

  let F := fun x ↦
        ToInternal.sectionEquiv (structureSheaf X) ((pushforward h).obj N) V
          (((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom h)).inv.app N).hom.app V
            (lift x))
  ∀ x y : P.obj V, F (x + y) = F x + F y :=
  sorry

/-- The universal section lift respects the structure-sheaf scalar action. -/
private theorem restrictSheafificationToPushforwardApp_smul {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (V : (smallEtaleSite X)ᵒᵖ) :
  let N := (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
    ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P)
  let lift := EtaleTopos.allChartLift U
    ((ToInternal.underlying (structureSheaf U)).obj N) ((etaleBaseChange h).obj V.unop)
    (restrictSheafificationPushforwardCone h P V.unop)

  let F := fun x ↦
        ToInternal.sectionEquiv (structureSheaf X) ((pushforward h).obj N) V
          (((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom h)).inv.app N).hom.app V
            (lift x))
  ∀ (r : (commStructureSheaf X).obj.obj V) (x : P.obj V), F (r • x) = r • F x :=
  sorry

/-- A presheaf section gives a section of the genuine direct image by the
full-chart universal lift, followed by the canonical module-forget comparison. -/
@[no_expose] def restrictSheafificationToPushforwardApp {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (V : (smallEtaleSite X)ᵒᵖ) :
    P.obj V ⟶
      (((pushforward h).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
          ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P))).val.obj V) :=
  let N := (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
    ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P)
  let lift := EtaleTopos.allChartLift U
    ((ToInternal.underlying (structureSheaf U)).obj N) ((etaleBaseChange h).obj V.unop)
    (restrictSheafificationPushforwardCone h P V.unop)
  ConcreteCategory.ofHom
    { toFun := fun x ↦
        ToInternal.sectionEquiv (structureSheaf X) ((pushforward h).obj N) V
          (((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom h)).inv.app N).hom.app V
            (lift x))
      map_add' := restrictSheafificationToPushforwardApp_add h P V
      map_smul' := restrictSheafificationToPushforwardApp_smul h P V }

/-- The universal section lifts commute with restriction of charts. -/
theorem restrictSheafificationToPushforwardPresheaf_naturality {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u}))
    {V W : (smallEtaleSite X)ᵒᵖ} (a : V ⟶ W) :
    P.map a ≫ (ModuleCat.restrictScalars ((structureSheaf X).obj.map a).hom).map
        (restrictSheafificationToPushforwardApp h P W) =
      restrictSheafificationToPushforwardApp h P V ≫ ((SheafOfModules.forget (structureSheaf X)).obj
      ((pushforward h).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
          ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P)))).map a :=
  sorry

/-- The actual section maps assemble into a presheaf morphism to `h_*` of
the sheafification of the restricted presheaf. -/
def restrictSheafificationToPushforwardPresheaf {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    P ⟶ (SheafOfModules.forget (structureSheaf X)).obj
      ((pushforward h).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
          ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P))) where
  app := restrictSheafificationToPushforwardApp h P
  naturality := fun {_ _} a ↦ restrictSheafificationToPushforwardPresheaf_naturality h P a

/-- Extend the specified presheaf morphism by the universal property of
module sheafification on `X`. -/
def restrictSheafificationToPushforward {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj P ⟶
      (pushforward h).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
          ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P)) :=
  ((PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 (structureSheaf X).obj)).homEquiv _ _).symm
      (restrictSheafificationToPushforwardPresheaf h P)

/-- The reverse comparison is the adjoint transpose of the actual sheaf map
to `h_*`, using the restriction adjunction's concrete unit and counit. -/
def restrictSheafificationInv {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    (restrictFunctor h).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj P) ⟶
      (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
        ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P) :=
  ((restrictAdjunction h).homEquiv _ _).symm (restrictSheafificationToPushforward h P)

/-- The reverse comparison sends the restriction of a sheafification-unit
section back to the sheafification unit of the restricted presheaf. -/
theorem restrictSheafificationInv_unit {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    restrictSheafificationUnit h P ≫
        (SheafOfModules.forget (structureSheaf U)).map (restrictSheafificationInv h P) =
      (PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (structureSheaf U).obj)).unit.app
          ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P) :=
  sorry

/-- Forward comparison followed by its explicitly constructed reverse is the identity. -/
theorem restrictSheafificationHom_inv_id {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    restrictSheafificationHom h P ≫ restrictSheafificationInv h P = 𝟙 _ :=
  sorry

/-- Reverse comparison followed by the canonical forward map is the identity. -/
theorem restrictSheafificationInv_hom_id {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    restrictSheafificationInv h P ≫ restrictSheafificationHom h P = 𝟙 _ :=
  sorry

/-- Étale restriction commutes with module sheafification with both maps explicit. -/
def restrictSheafificationIso {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
        ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P) ≅
      (restrictFunctor h).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj P) where
  hom := restrictSheafificationHom h P
  inv := restrictSheafificationInv h P
  hom_inv_id := restrictSheafificationHom_inv_id h P
  inv_hom_id := restrictSheafificationInv_hom_id h P

/-- The canonical forward comparison is invertible by its supplied explicit inverse. -/
instance restrictSheafificationHom_isIso {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    IsIso (restrictSheafificationHom h P) :=
  (restrictSheafificationIso h P).isIso_hom


end AlgebraicGeometry.AlgebraicSpace.Modules
