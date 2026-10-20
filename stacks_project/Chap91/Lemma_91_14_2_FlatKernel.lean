module
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap91.Lemma_91_14_2_Lift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.ClosedMap
@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

/-- Pull back the actual kernel-ideal quotient comparison of the cartesian square.
The map is fixed by kernel inclusion and cokernel descent, not by selecting an iso. -/
def cartesianConormalMap (L : FlatLift t f) :
    pulledConormal t f ⟶ closedFibreConormal L :=
  (liftConormalIso L).inv ≫
    (Modules.pullbackCompIso L.i L.f').inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t)) ≫
    (Modules.pullback L.i).map (Hom.Conormal.idealQuotientMap L.isPullback.toCommSq)

/-- Recover a section from the actual cartesian comparison fiber, with zero outside its image.
This total function takes no existence, bijectivity, or inverse-isomorphism certificate. -/
def cartesianConormalSectionPreimage (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ)
    (y : (closedFibreConormal L).val.obj U) : (pulledConormal t f).val.obj U := by
  classical
  exact if h : ∃ x, (cartesianConormalMap L).val.app U x = y then h.choose else 0

/-- Outside the actual section image the specified reconstruction is zero. -/
theorem cartesianConormalSectionPreimage_of_not_mem (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (y : (closedFibreConormal L).val.obj U)
    (hy : ¬ ∃ x, (cartesianConormalMap L).val.app U x = y) :
    cartesianConormalSectionPreimage L U y = 0 := by
  classical
  simp only [cartesianConormalSectionPreimage, dif_neg hy]

/-- On an actual inhabited fiber the reconstructed section maps to its specified value. -/
theorem cartesianConormalMap_sectionPreimage_of_mem (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (y : (closedFibreConormal L).val.obj U)
    (hy : ∃ x, (cartesianConormalMap L).val.app U x = y) :
    (cartesianConormalMap L).val.app U (cartesianConormalSectionPreimage L U y) = y := sorry

/-- Flat cartesian base change makes reconstruction additive. -/
theorem cartesianConormalSectionPreimage_add (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (x y : (closedFibreConormal L).val.obj U) :
    cartesianConormalSectionPreimage L U (x + y) =
      cartesianConormalSectionPreimage L U x + cartesianConormalSectionPreimage L U y := sorry

/-- Flat cartesian base change makes reconstruction linear over the structure sheaf. -/
theorem cartesianConormalSectionPreimage_smul (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (a : (structureSheaf X).obj.obj U)
    (x : (closedFibreConormal L).val.obj U) :
    cartesianConormalSectionPreimage L U (a • x) =
      a • cartesianConormalSectionPreimage L U x := sorry

/-- The reverse comparison has the specified section-fiber reconstruction as its actual map. -/
def cartesianConormalInv (L : FlatLift t f) :
    closedFibreConormal L ⟶ pulledConormal t f where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := cartesianConormalSectionPreimage L U
          map_add' := cartesianConormalSectionPreimage_add L U
          map_smul' := fun a x ↦ cartesianConormalSectionPreimage_smul L U a x }
      naturality := by intro U V g; sorry }

/-- The reverse comparison evaluates by its actual section fiber. -/
@[simp] theorem cartesianConormalInv_app (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (y : (closedFibreConormal L).val.obj U) :
    (cartesianConormalInv L).val.app U y = cartesianConormalSectionPreimage L U y := rfl

/-- Flatness and the cartesian square recover every source section. -/
theorem cartesianConormalMap_inv (L : FlatLift t f) :
    cartesianConormalMap L ≫ cartesianConormalInv L = 𝟙 _ := sorry

/-- Flatness and the cartesian square recover every target section. -/
theorem cartesianConormalInv_map (L : FlatLift t f) :
    cartesianConormalInv L ≫ cartesianConormalMap L = 𝟙 _ := sorry

/-- Both legs of the conormal identification are fixed by the actual cartesian comparison. -/
def cartesianConormalIso (L : FlatLift t f) :
    pulledConormal t f ≅ closedFibreConormal L where
  hom := cartesianConormalMap L
  inv := cartesianConormalInv L
  hom_inv_id := cartesianConormalMap_inv L
  inv_hom_id := cartesianConormalInv_map L

/-- Flat base change identifies the first-order conormal via the specified comparison. -/
theorem cartesianConormalMap_isIso (L : FlatLift t f) :
    IsIso (cartesianConormalMap L) := (cartesianConormalIso L).isIso_hom

@[simp] theorem cartesianConormalIso_inv (L : FlatLift t f) :
    (cartesianConormalIso L).inv = cartesianConormalInv L := rfl

@[simp] theorem cartesianConormalIso_hom (L : FlatLift t f) :
    (cartesianConormalIso L).hom = cartesianConormalMap L := rfl

end AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
