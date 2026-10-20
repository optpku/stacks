module

public import ReasLib.AlgebraicGeometry.GroupoidScheme

/-!
# Inversion in groupoid schemes

This module packages inversion as an automorphism of the arrow scheme and records its transport
of morphism properties between the source and target maps.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Inversion is an involutive automorphism of the arrow scheme of a groupoid scheme. -/
def inverseLeftIso {S : Scheme.{u}} (G : GroupoidScheme S) : G.R.left ≅ G.R.left := by
  -- Local instance justification (proof-local temporary data): point-groupoid data is used only to derive inversion involutivity.
  letI := G.pointGroupoid G.R
  let f : G.s ⟶ G.t := ⟨𝟙 G.R, by simp, by simp⟩
  have hInvInv : CategoryTheory.Groupoid.inv (CategoryTheory.Groupoid.inv f) = f := by
    simp [f]
  have hArrow :
      (CategoryTheory.Groupoid.inv (CategoryTheory.Groupoid.inv f)).arrow = f.arrow := by
    exact congrArg (fun p => p.arrow) hInvInv
  change ((f.arrow ≫ G.i) ≫ G.i = f.arrow) at hArrow
  have hiiLeft : G.i.left ≫ G.i.left = 𝟙 G.R.left := by
    simpa [f, Category.assoc] using congrArg Over.Hom.left hArrow
  exact
    { hom := G.i.left
      inv := G.i.left
      hom_inv_id := hiiLeft
      inv_hom_id := hiiLeft }

/-- Inversion identifies the source map with the target map in the arrow category of schemes. -/
def sourceTargetArrowIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    Arrow.mk G.s.left ≅ Arrow.mk G.t.left :=
  Arrow.isoMk (inverseLeftIso G) (Iso.refl _)
    (congrArg Over.Hom.left G.inverse_target)

/-- Every isomorphism-respecting morphism property holds for the source map of a groupoid scheme
if and only if it holds for the target map. -/
theorem sourceProperty_iff_targetProperty {S : Scheme.{u}} (G : GroupoidScheme S)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    P G.s.left ↔ P G.t.left :=
  P.arrow_mk_iso_iff (sourceTargetArrowIso G)

end AlgebraicGeometry.GroupoidScheme
