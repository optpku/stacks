module

public import ReasLib.Topology.Sheaf.Cohomology.Restriction
public import ReasLib.Topology.Sheaf.Cohomology.ClosedEmbedding
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Supported

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open TopCat.Sheaf.ClosedSubset.SectionsWithSupport

noncomputable section

universe u

namespace TopCat.Sheaf.Cohomology

variable {X : TopCat.{u}} {Z : Set X}

private def supportObjectIso (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u})
    (hF : restrictionToComplement hZ F = 0) : F ≅ object hZ F where
  hom := liftToObject hZ (𝟙 F) (by rw [Category.id_comp]; exact hF)
  inv := inclusion hZ F
  hom_inv_id := liftToObject_inclusion hZ (𝟙 F) (by rw [Category.id_comp]; exact hF)
  inv_hom_id := by
    apply (cancel_mono (inclusion hZ F)).1
    simp only [Category.assoc, liftToObject_inclusion, Category.comp_id, Category.id_comp]

/-- An explicit inverse to cohomological restriction to an open containing the closed support
of an abelian sheaf. -/
def restrictionInverseOfSupport (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u})
    (hF : restrictionToComplement hZ F = 0) (p : ℕ)
    (V : Opens X) (hV : Z ⊆ V) : F.H' p V ⟶ F.H' p ⊤ := by
  let G := supportedRestriction hZ F
  let α := supportObjectIso hZ F hF ≪≫ supportedRestrictionPushforwardIso hZ F
  have hpre : (Opens.map (TopCat.subsetInclusion Z)).obj V =
      (Opens.map (TopCat.subsetInclusion Z)).obj ⊤ := by
    ext x
    change (x.val ∈ V) ↔ (x.val ∈ (⊤ : Opens X))
    exact iff_of_true (hV x.property) (Set.mem_univ _)
  exact CategoryTheory.Sheaf.cohomologyMap α.hom p V ≫
    (CategoryTheory.Sheaf.ClosedEmbedding.comparisonIso (TopCat.subsetInclusion Z)
      hZ.isClosedEmbedding_subtypeVal G p V).hom ≫
    (eqToIso (congrArg (fun W ↦ G.H' p W) hpre)).hom ≫
    (CategoryTheory.Sheaf.ClosedEmbedding.comparisonIso (TopCat.subsetInclusion Z)
      hZ.isClosedEmbedding_subtypeVal G p ⊤).inv ≫
    CategoryTheory.Sheaf.cohomologyMap α.inv p ⊤

/-- Restriction followed by the supported restriction inverse is the identity. -/
theorem restriction_comp_inverseOfSupport (hZ : IsClosed Z)
    (F : X.Sheaf AddCommGrpCat.{u}) (hF : restrictionToComplement hZ F = 0)
    (p : ℕ) (V : Opens X) (hV : Z ⊆ V) :
    globalRestriction F p V ≫ restrictionInverseOfSupport hZ F hF p V hV = 𝟙 _ := sorry

/-- The supported restriction inverse followed by restriction is the identity. -/
theorem inverseOfSupport_comp_restriction (hZ : IsClosed Z)
    (F : X.Sheaf AddCommGrpCat.{u}) (hF : restrictionToComplement hZ F = 0)
    (p : ℕ) (V : Opens X) (hV : Z ⊆ V) :
    restrictionInverseOfSupport hZ F hF p V hV ≫ globalRestriction F p V = 𝟙 _ := sorry

/-- Cohomological restriction is an isomorphism on an open containing the closed support
of an abelian sheaf. -/
def restrictionIsoOfSupport (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u})
    (hF : restrictionToComplement hZ F = 0) (p : ℕ)
    (V : Opens X) (hV : Z ⊆ V) : F.H' p ⊤ ≅ F.H' p V where
  hom := globalRestriction F p V
  inv := restrictionInverseOfSupport hZ F hF p V hV
  hom_inv_id := restriction_comp_inverseOfSupport hZ F hF p V hV
  inv_hom_id := inverseOfSupport_comp_restriction hZ F hF p V hV

end TopCat.Sheaf.Cohomology
