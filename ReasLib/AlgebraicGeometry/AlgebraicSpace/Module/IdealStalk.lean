module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSheaf

/-!
# Étale stalks of ideal sheaves on algebraic spaces

A morphism of `𝒪_X`-modules into the structure sheaf induces a linear map from the
étale module stalk to the étale local ring. Its range is an ideal of
`etaleLocalRing X xbar`. Specializing to `Hom.idealSheafι` gives the stalk
`I_xbar` of the kernel ideal sheaf of a morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The additive presheaf of the unit `𝒪_X`-module is the additive underlying of `𝒪_X`. -/
def unitPresheafAddIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (SheafOfModules.unit (structureSheaf X)).val.presheaf ≅
      (structureSheaf X).obj ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro U V f
    ext a
    rfl)

/-- Components of `unitPresheafAddIso` are identity identifications of additive groups. -/
theorem unitPresheafAddIso_app {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (unitPresheafAddIso X).app U = Iso.refl _ :=
  rfl

/-- Additive comparison of the étale stalk of `𝒪_X` with the additive group of
`etaleLocalRing X xbar`. -/
def unitStalkAddIso {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    (forget₂ (ModuleCat (etaleLocalRing X xbar)) AddCommGrpCat.{u}).obj
      (stalkModuleCat xbar (SheafOfModules.unit (structureSheaf X))) ≅
      AddCommGrpCat.of (etaleLocalRing X xbar) :=
  (toSmallEtalePoint xbar).presheafFiber.mapIso (unitPresheafAddIso X) ≪≫
    ((toSmallEtalePoint xbar).presheafFiberCompIso
        (forget₂ RingCat.{u} AddCommGrpCat.{u})).app (structureSheaf X).obj

/-- `etaleLocalRing`-linearity of the additive unit-stalk comparison. -/
theorem unitStalkAddIso_map_smul {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) (r : etaleLocalRing X xbar)
    (m : stalkModuleCat xbar (SheafOfModules.unit (structureSheaf X))) :
    ConcreteCategory.hom (unitStalkAddIso xbar).hom (r • m) =
      r • ConcreteCategory.hom (unitStalkAddIso xbar).hom m :=
  sorry

/-- Canonical linear identification of the étale stalk of `𝒪_X` as a module with the
regular module on `etaleLocalRing X xbar`. -/
def unitStalkLinearEquiv {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    stalkModuleCat xbar (SheafOfModules.unit (structureSheaf X)) ≃ₗ[etaleLocalRing X xbar]
      etaleLocalRing X xbar where
  toAddEquiv := (unitStalkAddIso xbar).addCommGroupIsoToAddEquiv
  map_smul' := unitStalkAddIso_map_smul xbar

/-- The underlying function of `unitStalkLinearEquiv` is the additive comparison
`unitStalkAddIso`. -/
theorem unitStalkLinearEquiv_apply {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X)
    (m : stalkModuleCat xbar (SheafOfModules.unit (structureSheaf X))) :
    unitStalkLinearEquiv xbar m = (unitStalkAddIso xbar).hom m :=
  rfl

/-- Canonical linear map from the étale stalk of `𝒪_X` to the regular module on
`etaleLocalRing X xbar`. -/
abbrev unitStalkLinearMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    stalkModuleCat xbar (SheafOfModules.unit (structureSheaf X)) →ₗ[etaleLocalRing X xbar]
      etaleLocalRing X xbar :=
  (unitStalkLinearEquiv xbar).toLinearMap

/-- The map from the étale stalk of a module sheaf to the étale local ring induced by a
morphism into the structure module. -/
def stalkToRing {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {F : X.Modules} (f : F ⟶ SheafOfModules.unit (structureSheaf X)) :
    stalkModuleCat xbar F →ₗ[etaleLocalRing X xbar] etaleLocalRing X xbar :=
  unitStalkLinearMap xbar ∘ₗ (stalkModuleCatMap xbar f).hom

/-- The image ideal in `etaleLocalRing X xbar` of a module-sheaf morphism into the
structure module. -/
def stalkImageIdeal {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {F : X.Modules} (f : F ⟶ SheafOfModules.unit (structureSheaf X)) :
    Ideal (etaleLocalRing X xbar) :=
  LinearMap.range (stalkToRing xbar f)

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The inclusion of the associated ideal sheaf, viewed in the étale local ring through
the unit-stalk identification. -/
abbrev idealSheafStalkToRing {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (xbar : GeometricPoint X) :
    Modules.stalkModuleCat xbar (idealSheaf i) →ₗ[etaleLocalRing X xbar]
      etaleLocalRing X xbar :=
  Modules.stalkToRing xbar (idealSheafι i)

/-- The stalk of the associated ideal sheaf of `i` at a geometric point `xbar`, as an
ideal of `etaleLocalRing X xbar`. -/
def idealSheafStalkIdeal {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (xbar : GeometricPoint X) : Ideal (etaleLocalRing X xbar) :=
  Modules.stalkImageIdeal xbar (idealSheafι i)

/-- `idealSheafStalkIdeal` is the range of `idealSheafStalkToRing`. -/
theorem idealSheafStalkIdeal_eq {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (xbar : GeometricPoint X) :
    idealSheafStalkIdeal i xbar = LinearMap.range (idealSheafStalkToRing i xbar) :=
  rfl

/-- An element of `etaleLocalRing X xbar` lies in `idealSheafStalkIdeal i xbar` exactly
when it is the image of an element of the étale stalk of `Hom.idealSheaf i`. -/
theorem mem_idealSheafStalkIdeal_iff {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (xbar : GeometricPoint X) (a : etaleLocalRing X xbar) :
    a ∈ idealSheafStalkIdeal i xbar ↔
      ∃ s : Modules.stalkModuleCat xbar (idealSheaf i),
        idealSheafStalkToRing i xbar s = a :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.Hom
