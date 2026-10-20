module

public import Mathlib.Algebra.Group.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.Morphism
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped TensorProduct
open AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.Limits CategoryTheory.Functor
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Recover a morphism of commutative `𝒪_X`-modules from its universe lift. -/
def unliftCommModuleHom {F G : commModules X}
    (f : liftCommModule F ⟶ liftCommModule G) : F ⟶ G where
  val :=
    { app := fun U ↦
        ModuleCat.ofHom
          { toFun := fun x ↦ (f.val.app U (ULift.up x)).down
            map_add' := sorry
            map_smul' := sorry }
      naturality := sorry }

/-- Recover a morphism of `𝒪_X`-modules from a morphism of their universe lifts. -/
def unliftModuleHom {F G : X.Modules} (f : liftModule F ⟶ liftModule G) : F ⟶ G :=
  (commModulesEquivalence X).counitIso.inv.app F ≫
    (ofCommModules X).map (unliftCommModuleHom f) ≫
    (commModulesEquivalence X).counitIso.hom.app G

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Sections of `liftModule F` are universe-lifted commutative sections. -/
theorem liftModule_val_obj_eq {Y : AlgebraicSpace S} (F : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (Modules.liftModule F).val.obj U =
      Modules.liftedSection ((Modules.toCommModules Y).obj F) U :=
  sorry

/-- Reidentify a section of `liftModule F` as a universe-lifted commutative section. -/
def asLiftedSection {Y : AlgebraicSpace S} (F : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) (x : (Modules.liftModule F).val.obj U) :
    Modules.liftedSection ((Modules.toCommModules Y).obj F) U :=
  eqToHom (liftModule_val_obj_eq F U) x

/-- Reidentify a universe-lifted commutative section as a section of `liftModule F`. -/
def ofLiftedSection {Y : AlgebraicSpace S} (F : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ)
    (x : Modules.liftedSection ((Modules.toCommModules Y).obj F) U) :
    (Modules.liftModule F).val.obj U :=
  eqToHom (liftModule_val_obj_eq F U).symm x

/-- Universe-lift a commutative section of a commutative module sheaf. -/
def upLiftedCommSection {Y : AlgebraicSpace S} (F : Modules.commModules Y)
    (U : (smallEtaleSite Y)ᵒᵖ) (x : F.val.obj U) :
    Modules.liftedSection F U :=
  eqToHom (Modules.liftedSection_eq F U).symm (ULift.up x)

/-- Pointwise pure tensor of commutative module sections. -/
def commPointwiseTensor {Y : AlgebraicSpace S} {A B : Modules.commModules Y}
    (U : (smallEtaleSite Y)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    (PresheafOfModules.Monoidal.tensorObj A.val B.val).obj U :=
  x ⊗ₜ y

/-- Sheaf morphism from the sheafified pointwise tensor of `toComm F` and `toComm G` to
`toComm (F ⊗ G)`. -/
def commTensorComparison {Y : AlgebraicSpace S} (F G : Y.Modules) :
    (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y)).obj
      (PresheafOfModules.Monoidal.tensorObj
        ((Modules.toCommModules Y).obj F).val
        ((Modules.toCommModules Y).obj G).val) ⟶
      (Modules.toCommModules Y).obj (F ⊗ G) :=
  (Functor.Monoidal.μIso
      (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y))
      ((Modules.toCommModules Y).obj F).val
      ((Modules.toCommModules Y).obj G).val).inv ≫
    tensorHom
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
        ((Modules.toCommModules Y).obj F)).hom
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
        ((Modules.toCommModules Y).obj G)).hom ≫
    (Modules.commModulesEquivalence Y).unit.app
      (CategoryTheory.MonoidalCategory.tensorObj
        ((Modules.toCommModules Y).obj F)
        ((Modules.toCommModules Y).obj G))

/-- Pure tensor of already-unlifted commutative sections, as a section of `lift (F ⊗ G)`. -/
def commTensorToLift {Y : AlgebraicSpace S} (F G : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ)
    (x : ((Modules.toCommModules Y).obj F).val.obj U)
    (y : ((Modules.toCommModules Y).obj G).val.obj U) :
    Modules.liftedSection ((Modules.toCommModules Y).obj (F ⊗ G)) U :=
  upLiftedCommSection ((Modules.toCommModules Y).obj (F ⊗ G)) U
    ((commTensorComparison F G).val.app U
      ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commStructureSheaf Y)
          (PresheafOfModules.Monoidal.tensorObj
            ((Modules.toCommModules Y).obj F).val
            ((Modules.toCommModules Y).obj G).val)).app U
        (commPointwiseTensor U x y)))

/-- Universe-lift of a pure tensor of unlifted modules, as a section of
`lift (F ⊗ G)`. -/
def liftModuleTensorSection {Y : AlgebraicSpace S} (F G : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ)
    (x : (Modules.liftModule F).val.obj U)
    (y : (Modules.liftModule G).val.obj U) :
    (Modules.liftModule (F ⊗ G)).val.obj U :=
  ofLiftedSection (F ⊗ G) U
    (commTensorToLift F G U (asLiftedSection F U x).down (asLiftedSection G U y).down)

/-- Right-linear pure tensoring into `lift (F ⊗ G)`. -/
def liftModuleTensorRight {Y : AlgebraicSpace S} (F G : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ)
    (x : (Modules.liftModule F).val.obj U) :
    (Modules.liftModule G).val.obj U →ₗ[(commStructureSheafLift Y).obj.obj U]
      (Modules.liftModule (F ⊗ G)).val.obj U where
  toFun y := liftModuleTensorSection F G U x y
  map_add' := sorry
  map_smul' := sorry

/-- The objectwise bilinear map of lifted sections into `lift (F ⊗ G)`. -/
def liftModuleTensorApp {Y : AlgebraicSpace S} (F G : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (Modules.liftModule F).val.obj U →ₗ[(commStructureSheafLift Y).obj.obj U]
      (Modules.liftModule G).val.obj U →ₗ[(commStructureSheafLift Y).obj.obj U]
        (Modules.liftModule (F ⊗ G)).val.obj U where
  toFun x := liftModuleTensorRight F G U x
  map_add' := sorry
  map_smul' := sorry

/-- Compatible bilinear map of lifted sections representing `liftModuleTensorHom`. -/
def liftModuleTensorBilinear {Y : AlgebraicSpace S} (F G : Y.Modules) :
    PresheafOfModules.BilinearMap (commStructureSheafLift Y).obj
      (Modules.liftModule F).val (Modules.liftModule G).val
      (Modules.liftModule (F ⊗ G)).val where
  app := liftModuleTensorApp F G
  naturality := sorry

/-- The sheafification comparison identifying `lift F ⊗ lift G` with the sheafification of
the pointwise tensor of underlying lifted presheaves. -/
def liftModuleTensorSheafify {Y : AlgebraicSpace S} (F G : Y.Modules) :
    tensorObj (Modules.liftModule F) (Modules.liftModule G) ⟶
      (moduleSheafification (commStructureSheafLift Y)).obj
        (PresheafOfModules.Monoidal.tensorObj
          (Modules.liftModule F).val (Modules.liftModule G).val) :=
  tensorHom
      (moduleSheafificationValIso (commStructureSheafLift Y)
        (Modules.liftModule F)).inv
      (moduleSheafificationValIso (commStructureSheafLift Y)
        (Modules.liftModule G)).inv ≫
    Functor.LaxMonoidal.μ (moduleSheafification (commStructureSheafLift Y))
      (Modules.liftModule F).val (Modules.liftModule G).val

/-- The lax comparison `lift F ⊗ lift G ⟶ lift (F ⊗ G)`, obtained by universe-lifting the
pure tensor of the commutative presentations. -/
def liftModuleTensorHom {Y : AlgebraicSpace S} (F G : Y.Modules) :
    tensorObj (Modules.liftModule F) (Modules.liftModule G) ⟶
      Modules.liftModule (F ⊗ G) :=
  liftModuleTensorSheafify F G ≫
    (moduleSheafificationHomEquiv (commStructureSheafLift Y)
        (PresheafOfModules.Monoidal.tensorObj
          (Modules.liftModule F).val (Modules.liftModule G).val)
        (Modules.liftModule (F ⊗ G))).symm
      (liftModuleTensorBilinear F G).toHom

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
