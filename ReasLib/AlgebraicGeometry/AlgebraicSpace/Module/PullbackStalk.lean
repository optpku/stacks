module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk

/-!
# Pullback-stalk comparison for modules on algebraic spaces
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.Modules
open ModuleCat Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace Modules

variable {X Y : AlgebraicSpace S}

/-- Underlying type-valued sheaf of an `𝒪`-module on the small étale site. -/
def typeSheaf (Z : AlgebraicSpace S) :
    Z.Modules ⥤ Sheaf (smallEtaleTopology Z) (Type u) :=
  SheafOfModules.toSheaf (structureSheaf Z) ⋙
    sheafCompose (smallEtaleTopology Z) (forget AddCommGrpCat.{u})

/-- The additive group of an étale module stalk is the site-point fibre of the underlying
additive presheaf. -/
def stalkModuleCat_addIso {Z : AlgebraicSpace S} (xbar : GeometricPoint Z) (F : Z.Modules) :
    (forget₂ (ModuleCat (etaleLocalRing Z xbar)) AddCommGrpCat.{u}).obj (stalkModuleCat xbar F) ≅
      (toSmallEtalePoint xbar).presheafFiber.obj F.val.presheaf :=
  Iso.refl _

/-- The underlying type of an étale module stalk identifies with the type-valued sheaf fibre. -/
def stalkModuleCat_typeIso {Z : AlgebraicSpace S} (xbar : GeometricPoint Z) (F : Z.Modules) :
    (forget (ModuleCat (etaleLocalRing Z xbar))).obj (stalkModuleCat xbar F) ≅
      (toSmallEtalePoint xbar).sheafFiber.obj ((typeSheaf Z).obj F) :=
  (forget AddCommGrpCat.{u}).mapIso (stalkModuleCat_addIso xbar F) ≪≫
    ((toSmallEtalePoint xbar).sheafFiberCompIso (forget AddCommGrpCat.{u})).symm.app
      ((SheafOfModules.toSheaf (structureSheaf Z)).obj F)

/-- Additive comparison from the stalk of `𝒢` at `ȳ` to the stalk of `f* 𝒢` at `x̄`. -/
def morphismPullbackStalkAddHom (f : X ⟶ Y) (G : Y.Modules) (xbar : GeometricPoint X) :
    AddCommGrpCat.of (stalkModuleCat (xbar.map f) G) ⟶
      AddCommGrpCat.of (stalkModuleCat xbar ((pullback f).obj G)) :=
  AddCommGrpCat.ofHom
    { toFun := fun m ↦
        (stalkModuleCat_typeIso xbar ((pullback f).obj G)).inv
          ((toSmallEtalePoint xbar).sheafFiber.map
              (((morphismOfTopoi f).adjunction.homEquiv
                  ((typeSheaf Y).obj G)
                  ((typeSheaf X).obj ((pullback f).obj G))).symm
                ((typeSheaf Y).map ((Modules.pullbackPushforwardAdjunction f).unit.app G) ≫
                  (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).hom.app
                    ((pullback f).obj G)))
            ((typeInverseImageStalkInv f xbar).app ((typeSheaf Y).obj G)
              ((stalkModuleCat_typeIso (xbar.map f) G).hom m)))
      map_zero' := sorry
      map_add' := sorry }

/-- The `𝒪_{Y, ȳ}`-linear comparison from `𝒢_ȳ` to the stalk of `f* 𝒢` at `x̄`, after
restricting scalars along `etaleLocalRingMap`. -/
def morphismPullbackStalkUnitHom (f : X ⟶ Y) (G : Y.Modules) (xbar : GeometricPoint X) :
    stalkModuleCat (xbar.map f) G ⟶
      (restrictScalars (etaleLocalRingMap f xbar)).obj
        (stalkModuleCat xbar ((pullback f).obj G)) :=
  (semilinearMapAddEquiv (etaleLocalRingMap f xbar)
      (stalkModuleCat (xbar.map f) G)
      (stalkModuleCat xbar ((pullback f).obj G)))
    { toFun := (morphismPullbackStalkAddHom f G xbar).hom
      map_add' := (morphismPullbackStalkAddHom f G xbar).hom.map_add
      map_smul' := sorry }

/-- `morphismPullbackStalkUnitHom` is `𝒪_{Y, ȳ}`-linear. -/
theorem morphismPullbackStalkUnitHom_smul (f : X ⟶ Y) (G : Y.Modules) (xbar : GeometricPoint X)
    (r : etaleLocalRing Y (xbar.map f)) (m : stalkModuleCat (xbar.map f) G) :
    morphismPullbackStalkUnitHom f G xbar (r • m) =
      etaleLocalRingMap f xbar r • morphismPullbackStalkUnitHom f G xbar m :=
  sorry

/-- Canonical comparison
`(f* 𝒢)_x̄` against `𝒢_ȳ ⊗_{𝒪_{Y, ȳ}} 𝒪_{X, x̄}`,
obtained by extending scalars along `etaleLocalRingMap`. -/
def pullbackStalkComparison (f : X ⟶ Y) (G : Y.Modules) (xbar : GeometricPoint X) :
    (extendScalars (etaleLocalRingMap f xbar)).obj (stalkModuleCat (xbar.map f) G) ⟶
      stalkModuleCat xbar ((pullback f).obj G) :=
  ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (etaleLocalRingMap f xbar)
    (morphismPullbackStalkUnitHom f G xbar)

/-- `pullbackStalkComparison` is the adjunction transpose of `morphismPullbackStalkUnitHom`. -/
theorem pullbackStalkComparison_def (f : X ⟶ Y) (G : Y.Modules) (xbar : GeometricPoint X) :
    pullbackStalkComparison f G xbar =
      ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (etaleLocalRingMap f xbar)
        (morphismPullbackStalkUnitHom f G xbar) :=
  rfl

/-- For a quasi-coherent module on the target of a morphism of algebraic spaces, extension
of scalars of its stalk at the image geometric point is canonically isomorphic to the stalk
of its pullback at the original point. -/
instance pullbackStalkComparison_isIso (f : X ⟶ Y) (G : Y.Modules) [G.IsQuasicoherent]
    (xbar : GeometricPoint X) :
    IsIso (pullbackStalkComparison f G xbar) :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
