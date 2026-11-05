module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Pointed

/-!
# Represented pointed Picard maps

A representation is supplied explicitly. Consequently this interface works
with any representing scheme and any subfunctor containing the pointed map;
it does not select a second Picard model or bake in curve degree, a ground
field, or a theorem asserting representability.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section
universe u

namespace AlgebraicGeometry.RelativePicard

variable {S : Scheme.{u}} (X : Over S)
variable [IsSeparated X.hom] [SmoothOfRelativeDimension 1 X.hom]

/-- The pointed map into any supplied representation of the Picard fppf sheaf. -/
noncomputable def pointedMapWith {Y : Over S}
    (R : (functor X).obj.RepresentableBy Y) (P : 𝟙_ (Over S) ⟶ X) : X ⟶ Y :=
  R.homEquiv.symm ((pointedFppfMap X P).app (Opposite.op X) (ULift.up (𝟙 X)))

/-- The represented map realizes the canonical pointed Picard section. -/
@[simp]
theorem pointedMapWith_homEquiv {Y : Over S}
    (R : (functor X).obj.RepresentableBy Y) (P : 𝟙_ (Over S) ⟶ X) :
    R.homEquiv (pointedMapWith X R P) =
      (pointedFppfMap X P).app (Opposite.op X) (ULift.up (𝟙 X)) :=
  R.homEquiv.apply_symm_apply _

/-- Changing the representing model preserves the pointed map canonically. -/
theorem pointedMapWith_changeRepresentation {Y Y' : Over S}
    (R : (functor X).obj.RepresentableBy Y)
    (R' : (functor X).obj.RepresentableBy Y') (P : 𝟙_ (Over S) ⟶ X) :
    pointedMapWith X R P ≫ (R.uniqueUpToIso R').hom = pointedMapWith X R' P := by
  sorry

/-- The pointed map into a supplied representation of any containing subfunctor. -/
noncomputable def pointedMapToSubfunctorWith {Y : Over S}
    (F : Subfunctor (functor X).obj) (R : F.toFunctor.RepresentableBy Y)
    (P : 𝟙_ (Over S) ⟶ X) (hP : Subfunctor.range (pointedFppfMap X P) ≤ F) : X ⟶ Y :=
  R.homEquiv.symm
    ((Subfunctor.lift (pointedFppfMap X P) hP).app (Opposite.op X) (ULift.up (𝟙 X)))

end AlgebraicGeometry.RelativePicard
