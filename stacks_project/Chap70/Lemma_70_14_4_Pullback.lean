module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap70.Lemma_70_14_2_Torsion
public import stacks_project.Chap69.Lemma_69_17_2_Pullback

/-!
# Inverse-image ideals on algebraic spaces

The inverse-image ideal of `I ⊂ 𝒪_Y` along `f : X ⟶ Y` is the image of the
canonical map `f^* I ⟶ 𝒪_X` obtained from `f^* I ⟶ f^* 𝒪_Y` and the unit
comparison `f^* 𝒪_Y ⟶ 𝒪_X`.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

/-- The type-valued sheaf underlying the structure module `𝒪_X` compares with the
underlying structure sheaf of the small étale ringed site. -/
def unitUnderlyingIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
      (SheafOfModules.unit (structureSheaf X)) ≅
      RingedSite.Hom.underlyingStructureSheaf (ringedSite X) where
  hom :=
    { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  inv :=
    { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical morphism `𝒪_Y ⟶ f_* 𝒪_X` of `𝒪_Y`-modules associated to a
morphism of algebraic spaces. -/
def unitToPushforwardObjUnit {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    SheafOfModules.unit (structureSheaf Y) ⟶
      (pushforward f).obj (SheafOfModules.unit (structureSheaf X)) :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf Y)
    ((unitUnderlyingIso Y).hom ≫
      (ringedToposHom f).underlyingDirectImageMap ≫
      (ringedToposHom f).toTopos.pushforward.map (unitUnderlyingIso X).inv ≫
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).inv.app
        (SheafOfModules.unit (structureSheaf X)))
    sorry sorry

/-- The canonical comparison `f^* 𝒪_Y ⟶ 𝒪_X` of structure modules. -/
def pullbackObjUnitToUnit {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (pullback f).obj (SheafOfModules.unit (structureSheaf Y)) ⟶
      SheafOfModules.unit (structureSheaf X) :=
  ((pullbackPushforwardAdjunction f).homEquiv
      (SheafOfModules.unit (structureSheaf Y))
      (SheafOfModules.unit (structureSheaf X))).symm
    (unitToPushforwardObjUnit f)

/-- `pullbackObjUnitToUnit f` is the adjunct of `unitToPushforwardObjUnit f`. -/
theorem pullbackObjUnitToUnit_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    pullbackObjUnitToUnit f =
      ((pullbackPushforwardAdjunction f).homEquiv
          (SheafOfModules.unit (structureSheaf Y))
          (SheafOfModules.unit (structureSheaf X))).symm
        (unitToPushforwardObjUnit f) :=
  rfl

end Modules

namespace IdealSubobject

/-- Inverse image of a quasi-coherent ideal sheaf remains quasi-coherent as an
`𝒪`-module on the source. -/
instance pullback_isQuasicoherent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : IdealSubobject Y) [(I : Y.Modules).IsQuasicoherent] (f : X ⟶ Y) :
    (I.pullback f : X.Modules).IsQuasicoherent :=
  sorry

/-- Inverse image of a finite type ideal sheaf remains of finite type as an
`𝒪`-module on the source. -/
instance pullback_isFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : IdealSubobject Y) [(I : Y.Modules).IsFiniteType] (f : X ⟶ Y) :
    (I.pullback f : X.Modules).IsFiniteType :=
  sorry

end IdealSubobject

end AlgebraicGeometry.AlgebraicSpace
