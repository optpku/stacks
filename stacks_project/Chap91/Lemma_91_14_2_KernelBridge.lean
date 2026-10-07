module
public import stacks_project.Chap91.Lemma_91_14_2_FlatKernel
public import stacks_project.Chap76.Lemma_76_17_1_Difference
@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.CanonicalKernel
variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

abbrev projection (L : FlatLift t f) :=
  (forgetSpacesRing X).map (closedStructureSheaf_structureMap L.i)

abbrev restrictedKernel (L : FlatLift t f) :=
  (restrictSpacesAdd X).obj (kernel (projection L))

/-- The actual first-order ideal inclusion, after the cartesian conormal comparison. -/
def inclusion (L : FlatLift t f) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) ⟶
      (restrictSpacesAdd X).obj ((forgetSpacesRing X).obj (closedStructureSheaf L.i)) :=
  (SheafOfModules.toSheaf (structureSheaf X)).map
      (cartesianConormalMap L ≫ pullbackQuotientToConormal L.i) ≫ conormalInclusion L.i

/-- The geometric first-order ideal inclusion lands in the kernel of the structure map. -/
theorem inclusion_comp_projection (L : FlatLift t f) :
    inclusion L ≫ (restrictSpacesAdd X).map (projection L) = 0 := sorry

/-- Restriction of sheaves to the small étale site preserves this kernel. -/
instance preservesProjectionKernel (L : FlatLift t f) :
    PreservesLimit (parallelPair (projection L) 0) (restrictSpacesAdd X) := sorry

/-- The kernel comparison is the universal lift of the concrete ideal inclusion. -/
def comparison (L : FlatLift t f) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) ⟶
      restrictedKernel L :=
  kernel.lift ((restrictSpacesAdd X).map (projection L)) (inclusion L)
      (inclusion_comp_projection L) ≫
    (PreservesKernel.iso (restrictSpacesAdd X) (projection L)).inv

/-- The chosen kernel comparison recovers the fixed geometric ideal inclusion. -/
theorem comparison_fac (L : FlatLift t f) :
    comparison L ≫ (restrictSpacesAdd X).map (kernel.ι (projection L)) = inclusion L := by
  simp only [comparison, Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]

/-- Flatness makes this specified kernel comparison invertible. -/
theorem comparison_isIso (L : FlatLift t f) : IsIso (comparison L) := sorry

/-- Canonical identification, fixed by the actual kernel inclusion. -/
def iso (L : FlatLift t f) : restrictedKernel L ≅
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) :=
  -- Local instance justification (proof-local temporary data): invert the kernel lift of the specified geometric ideal inclusion.
  letI := comparison_isIso L
  (asIso (comparison L)).symm

@[simp] theorem iso_inv (L : FlatLift t f) : (iso L).inv = comparison L := rfl
end AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.CanonicalKernel
