module
public import stacks_project.Chap91.Lemma_91_14_2_LiftAlgebra
public import stacks_project.Chap91.Lemma_91_14_2_KernelBridge
public import stacks_project.Chap91.«91_13_0_1_Solution»
@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
open AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
open SheafOfModules.RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.SmallKernel
variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

abbrev unitAdd (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :=
  (SheafOfModules.toSheaf (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) A)).obj
    (unitModule (smallEtaleTopology X) A)

/-- The structure module has the same underlying sections as the ring. -/
def unitUnderlyingTypeIso (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (forgetSpacesAddType X).obj (unitAdd A) ≅
      (sheafCompose (smallEtaleTopology X) (forget CommRingCat.{u})).obj A where
  hom := { hom := { app := fun _ ↦ 𝟙 _, naturality := sorry } }
  inv := { hom := { app := fun _ ↦ 𝟙 _, naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The small/spaces comparison is the composite of the existing adjunction mates,
ring-forget comparison, and the fixed underlying structure-module identification. -/
def restrictionTypeComparison (L : FlatLift t f) :
    (forgetSpacesAddType X).obj ((restrictSpacesAdd X).obj
      ((forgetSpacesRing X).obj (closedStructureSheaf L.i))) ⟶
    (forgetSpacesAddType X).obj (unitAdd (liftAlgebra L)) :=
  restrictInverseImageTypeHom L.i ≫
    inv (inverseImageForgetAddHom L.i
      ((sheafCompose (smallEtaleTopology L.space) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf L.space))) ≫
    (morphismOfTopoi L.i).ringInverseImageForgetIso.inv.app (structureSheaf L.space) ≫
    eqToHom (congrArg
      (fun R : Sheaf (smallEtaleTopology X) RingCat.{u} ↦
        (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj R)
      (commInverseImageStructureSheaf_forget L.i).symm) ≫
    (unitUnderlyingTypeIso (liftAlgebra L)).inv

/-- The comparison of inverse-image rings preserves their additive structure. -/
theorem restrictionTypeComparison_add (L : FlatLift t f) :
    typeHomIsAdditive (restrictionTypeComparison L) := sorry

def restrictionAddComparison (L : FlatLift t f) :
    (restrictSpacesAdd X).obj ((forgetSpacesRing X).obj (closedStructureSheaf L.i)) ⟶
    unitAdd (liftAlgebra L) :=
  addHomOfType (restrictionTypeComparison L) (hf := restrictionTypeComparison_add L)

/-- The specified geometric ideal inclusion in the small-site extension algebra. -/
def inclusion (L : FlatLift t f) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) ⟶
      unitAdd (liftAlgebra L) :=
  CanonicalKernel.inclusion L ≫ restrictionAddComparison L

theorem inclusion_comp_projection (L : FlatLift t f) :
    inclusion L ≫
      (SheafOfModules.toSheaf (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (liftAlgebra L))).map
        (KernelIdeal.map (liftAlgebraProj L)) = 0 := sorry

/-- The additive comparison is kernel.lift, followed by the specified target-module descent. -/
def kernelComparisonAdd (L : FlatLift t f) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) ⟶
      (SheafOfModules.toSheaf (structureSheaf X)).obj
        (kernelModule (liftAlgebraProj L) (liftAlgebra_squareZero L)) :=
  KernelIdeal.additiveLift (liftAlgebraProj L) (inclusion L) (inclusion_comp_projection L) ≫
    (kernelModuleForgetIso (liftAlgebraProj L) (liftAlgebra_squareZero L)).inv

/-- The module comparison has the above fixed section function. -/
def kernelComparison (L : FlatLift t f) :
    pulledConormal t f ⟶ kernelModule (liftAlgebraProj L) (liftAlgebra_squareZero L) where
  val := PresheafOfModules.homMk
    ((sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u}).map (kernelComparisonAdd L))
    (fun _ _ _ ↦ sorry)

/-- The cartesian, flat first-order square identifies its two kernel modules by this map. -/
theorem kernelComparison_isIso (L : FlatLift t f) : IsIso (kernelComparison L) := sorry

def kernelIso (L : FlatLift t f) :
    kernelModule (liftAlgebraProj L) (liftAlgebra_squareZero L) ≅ pulledConormal t f :=
  -- Local instance justification (proof-local temporary data): invert the linear map constructed from the fixed small-site kernel inclusion.
  letI := kernelComparison_isIso L
  (asIso (kernelComparison L)).symm

@[simp] theorem kernelIso_inv (L : FlatLift t f) : (kernelIso L).inv = kernelComparison L := rfl
end AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.SmallKernel
