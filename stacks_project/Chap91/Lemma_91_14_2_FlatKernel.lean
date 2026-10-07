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
    (Modules.pullbackComp L.i L.f').inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t)) ≫
    (Modules.pullback L.i).map (Hom.Conormal.idealQuotientMap L.isPullback.toCommSq)

/-- Flat base change identifies the first-order conormal via the specified comparison. -/
theorem cartesianConormalMap_isIso (L : FlatLift t f) :
    IsIso (cartesianConormalMap L) := sorry

/-- The conormal identification retains the actual cartesian comparison as its forward map. -/
def cartesianConormalIso (L : FlatLift t f) :
    pulledConormal t f ≅ closedFibreConormal L :=
  -- Local instance justification (proof-local temporary data): invert this fixed cartesian conormal map using its flat base-change law.
  letI := cartesianConormalMap_isIso L
  asIso (cartesianConormalMap L)

@[simp] theorem cartesianConormalIso_hom (L : FlatLift t f) :
    (cartesianConormalIso L).hom = cartesianConormalMap L := rfl

end AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
