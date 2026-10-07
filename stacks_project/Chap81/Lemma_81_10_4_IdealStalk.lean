module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Defs
public import stacks_project.Chap66.Lemma_66_29_4_Stalk
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf

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

/-- Naturality of the identity comparison from the unit `𝒪_X`-module to the additive
underlying of `𝒪_X`. -/
theorem unitPresheafAddIso_naturality {S : Scheme.{u}} (X : AlgebraicSpace S)
    {U V : (smallEtaleSite X)ᵒᵖ} (f : U ⟶ V) :
    (Iso.refl ((SheafOfModules.unit (structureSheaf X)).val.presheaf.obj U)).hom ≫
      ((structureSheaf X).obj ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}).map f =
    (SheafOfModules.unit (structureSheaf X)).val.presheaf.map f ≫
      (Iso.refl ((SheafOfModules.unit (structureSheaf X)).val.presheaf.obj V)).hom :=
  sorry

/-- The additive presheaf of the unit `𝒪_X`-module is the additive underlying of `𝒪_X`. -/
def unitPresheafAddIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (SheafOfModules.unit (structureSheaf X)).val.presheaf ≅
      (structureSheaf X).obj ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} f ↦ unitPresheafAddIso_naturality X f)

/-- Components of `unitPresheafAddIso` are identity identifications of additive groups. -/
theorem unitPresheafAddIso_app {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (unitPresheafAddIso X).app U = Iso.refl _ :=
  sorry

/-- Additive comparison of the étale stalk of `𝒪_X` with the additive group of
`etaleLocalRing X xbar`. -/
def unitStalkAddIso {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    (forget₂ (ModuleCat (etaleLocalRing X xbar)) AddCommGrpCat.{u}).obj
      (stalkModuleCat xbar (SheafOfModules.unit (structureSheaf X))) ≅
      AddCommGrpCat.of (etaleLocalRing X xbar) :=
  (toSmallEtalePoint xbar).presheafFiber.mapIso (unitPresheafAddIso X) ≪≫
    ((toSmallEtalePoint xbar).presheafFiberCompIso
        (forget₂ RingCat.{u} AddCommGrpCat.{u})).app (structureSheaf X).obj

/-- `unitStalkAddIso` is the site-point fiber of `unitPresheafAddIso`, compared with the
forgetful fiber of the étale local ring. -/
theorem unitStalkAddIso_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    unitStalkAddIso xbar =
      (toSmallEtalePoint xbar).presheafFiber.mapIso (unitPresheafAddIso X) ≪≫
        ((toSmallEtalePoint xbar).presheafFiberCompIso
            (forget₂ RingCat.{u} AddCommGrpCat.{u})).app (structureSheaf X).obj :=
  sorry

/-- Left inverse law for the additive unit-stalk comparison. -/
theorem unitStalkLinearEquiv_left_inv {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X)
    (m : stalkModuleCat xbar (SheafOfModules.unit (structureSheaf X))) :
    ConcreteCategory.hom (unitStalkAddIso xbar).inv
      (ConcreteCategory.hom (unitStalkAddIso xbar).hom m) = m :=
  sorry

/-- Right inverse law for the additive unit-stalk comparison. -/
theorem unitStalkLinearEquiv_right_inv {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) (a : etaleLocalRing X xbar) :
    ConcreteCategory.hom (unitStalkAddIso xbar).hom
      (ConcreteCategory.hom (unitStalkAddIso xbar).inv a) = a :=
  sorry

/-- Additivity of the additive unit-stalk comparison. -/
theorem unitStalkLinearEquiv_map_add {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X)
    (m n : stalkModuleCat xbar (SheafOfModules.unit (structureSheaf X))) :
    ConcreteCategory.hom (unitStalkAddIso xbar).hom (m + n) =
      ConcreteCategory.hom (unitStalkAddIso xbar).hom m +
        ConcreteCategory.hom (unitStalkAddIso xbar).hom n :=
  sorry

/-- `etaleLocalRing`-linearity of the additive unit-stalk comparison. -/
theorem unitStalkLinearEquiv_map_smul {S : Scheme.{u}} {X : AlgebraicSpace S}
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
  toFun := ConcreteCategory.hom (unitStalkAddIso xbar).hom
  invFun := ConcreteCategory.hom (unitStalkAddIso xbar).inv
  left_inv := unitStalkLinearEquiv_left_inv xbar
  right_inv := unitStalkLinearEquiv_right_inv xbar
  map_add' := unitStalkLinearEquiv_map_add xbar
  map_smul' := unitStalkLinearEquiv_map_smul xbar

/-- The underlying function of `unitStalkLinearEquiv` is the additive comparison
`unitStalkAddIso`. -/
theorem unitStalkLinearEquiv_apply {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X)
    (m : stalkModuleCat xbar (SheafOfModules.unit (structureSheaf X))) :
    unitStalkLinearEquiv xbar m = (unitStalkAddIso xbar).hom m :=
  sorry

/-- Canonical linear map from the étale stalk of `𝒪_X` to the regular module on
`etaleLocalRing X xbar`. -/
abbrev unitStalkLinearMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    stalkModuleCat xbar (SheafOfModules.unit (structureSheaf X)) →ₗ[etaleLocalRing X xbar]
      etaleLocalRing X xbar :=
  (unitStalkLinearEquiv xbar).toLinearMap

/-- `unitStalkLinearMap` is the linear map of `unitStalkLinearEquiv`. -/
theorem unitStalkLinearMap_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    unitStalkLinearMap xbar = (unitStalkLinearEquiv xbar).toLinearMap :=
  sorry

/-- The map from the étale stalk of a module sheaf to the étale local ring induced by a
morphism into the structure module. -/
def stalkToRing {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {F : X.Modules} (f : F ⟶ SheafOfModules.unit (structureSheaf X)) :
    stalkModuleCat xbar F →ₗ[etaleLocalRing X xbar] etaleLocalRing X xbar :=
  unitStalkLinearMap xbar ∘ₗ (stalkModuleCatMap xbar f).hom

/-- `stalkToRing` is `unitStalkLinearMap` composed with the étale stalk of `f`. -/
theorem stalkToRing_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {F : X.Modules} (f : F ⟶ SheafOfModules.unit (structureSheaf X)) :
    stalkToRing xbar f = unitStalkLinearMap xbar ∘ₗ (stalkModuleCatMap xbar f).hom :=
  sorry

/-- The image ideal in `etaleLocalRing X xbar` of a module-sheaf morphism into the
structure module. -/
def stalkImageIdeal {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {F : X.Modules} (f : F ⟶ SheafOfModules.unit (structureSheaf X)) :
    Ideal (etaleLocalRing X xbar) :=
  LinearMap.range (stalkToRing xbar f)

/-- `stalkImageIdeal` is the range of `stalkToRing`. -/
theorem stalkImageIdeal_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) {F : X.Modules}
    (f : F ⟶ SheafOfModules.unit (structureSheaf X)) :
    stalkImageIdeal xbar f = LinearMap.range (stalkToRing xbar f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The inclusion of the associated ideal sheaf, viewed in the étale local ring through
the unit-stalk identification. -/
abbrev idealSheafStalkToRing {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (xbar : GeometricPoint X) :
    Modules.stalkModuleCat xbar (idealSheaf i) →ₗ[etaleLocalRing X xbar]
      etaleLocalRing X xbar :=
  Modules.stalkToRing xbar (idealSheafι i)

/-- `idealSheafStalkToRing` is `Modules.stalkToRing` of `idealSheafι`. -/
theorem idealSheafStalkToRing_eq {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (xbar : GeometricPoint X) :
    idealSheafStalkToRing i xbar = Modules.stalkToRing xbar (idealSheafι i) :=
  sorry

/-- The stalk of the associated ideal sheaf of `i` at a geometric point `xbar`, as an
ideal of `etaleLocalRing X xbar`. -/
def idealSheafStalkIdeal {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (xbar : GeometricPoint X) : Ideal (etaleLocalRing X xbar) :=
  Modules.stalkImageIdeal xbar (idealSheafι i)

/-- `idealSheafStalkIdeal` is the range of `idealSheafStalkToRing`. -/
theorem idealSheafStalkIdeal_eq {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (xbar : GeometricPoint X) :
    idealSheafStalkIdeal i xbar = LinearMap.range (idealSheafStalkToRing i xbar) :=
  sorry

/-- An element of `etaleLocalRing X xbar` lies in `idealSheafStalkIdeal i xbar` exactly
when it is the image of an element of the étale stalk of `Hom.idealSheaf i`. -/
theorem mem_idealSheafStalkIdeal_iff {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (xbar : GeometricPoint X) (a : etaleLocalRing X xbar) :
    a ∈ idealSheafStalkIdeal i xbar ↔
      ∃ s : Modules.stalkModuleCat xbar (idealSheaf i),
        idealSheafStalkToRing i xbar s = a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
