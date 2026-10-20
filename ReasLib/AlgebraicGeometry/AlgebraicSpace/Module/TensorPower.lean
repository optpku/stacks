module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.SectionTensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Graded
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.StructureModule
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped TensorProduct
open AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Tensor powers of an `𝒪_Y`-module based at the structure module `𝒪_Y`. -/
abbrev tensorPowerUnit {Y : AlgebraicSpace S} (L : Y.Modules) (n : ℕ) : Y.Modules :=
  tensorPowerWithDegreeZero (SheafOfModules.unit (structureSheaf Y)) L n

/-- The zeroth unit-based tensor power is the structure module. -/
theorem tensorPowerUnit_zero {Y : AlgebraicSpace S} (L : Y.Modules) :
    tensorPowerUnit L 0 = SheafOfModules.unit (structureSheaf Y) :=
  tensorPowerWithDegreeZero_zero (SheafOfModules.unit (structureSheaf Y)) L

/-- The successor unit-based tensor power is left tensor with `L`. -/
theorem tensorPowerUnit_succ {Y : AlgebraicSpace S} (L : Y.Modules) (n : ℕ) :
    tensorPowerUnit L (n + 1) = L ⊗ tensorPowerUnit L n :=
  rfl

/-- Concatenation of unit-based tensor powers. -/
def tensorPowerUnitAddIso {Y : AlgebraicSpace S} (L : Y.Modules) (i j : ℕ) :
    tensorPowerUnit L i ⊗ tensorPowerUnit L j ≅ tensorPowerUnit L (i + j) :=
  tensorPowerWithDegreeZeroAddIso (Modules.structureModuleIsoTensorUnit Y) L i j

/-- The induced map of unit-based tensor powers along a module morphism. -/
def tensorPowerUnitMap {Y : AlgebraicSpace S} {L L' : Y.Modules} (β : L ⟶ L') (n : ℕ) :
    tensorPowerUnit L n ⟶ tensorPowerUnit L' n :=
  tensorPowerWithDegreeZeroMap (SheafOfModules.unit (structureSheaf Y)) β n

/-- Universe-lifted tensor powers of an `𝒪_Y`-module. -/
abbrev tensorPowerSheaf {Y : AlgebraicSpace S} (L : Y.Modules) (n : ℕ) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift Y) :=
  TensorPower.sheaf (commStructureSheafLift Y) (Modules.liftModule L) n

/-- The structure-sheaf unit of `Y` as a local section of its universe lift. -/
def liftedUnitSection (Y : AlgebraicSpace S) (U : (smallEtaleSite Y)ᵒᵖ) :
    (unitModule (smallEtaleTopology Y) (commStructureSheafLift Y)).val.obj U :=
  TensorPower.oneSection (commStructureSheafLift Y)
    (Modules.liftModule (SheafOfModules.unit (structureSheaf Y))) U

/-- Pullback of a unit-based tensor power is the tensor power of the pullback, using the
structure-module comparison in degree zero and the pullback laxator in successor degrees. -/
def pullbackTensorPowerHom {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (L : Y.Modules) :
    (n : ℕ) →
      (Modules.pullback h).obj (tensorPowerUnit L n) ⟶
        tensorPowerUnit ((Modules.pullback h).obj L) n :=
  Nat.rec
    (eqToHom (congrArg (Modules.pullback h).obj (tensorPowerUnit_zero L)) ≫
      (pullbackMonoidalUnitIso h).hom ≫
        eqToHom (tensorPowerUnit_zero ((Modules.pullback h).obj L)).symm)
    (fun n rec ↦
      eqToHom (congrArg (Modules.pullback h).obj (tensorPowerUnit_succ L n)) ≫
        pullbackTensorOplax h L (tensorPowerUnit L n) ≫
          (𝟙 ((Modules.pullback h).obj L) ⊗ₘ rec) ≫
            eqToHom (tensorPowerUnit_succ ((Modules.pullback h).obj L) n).symm)

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
