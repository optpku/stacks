module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import ReasLib.CategoryTheory.Sites.Torsor.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleComparison

/-!
# Torsors on the étale and pro-étale sites

Inverse image along the inclusion of small sites induces the canonical comparison
on isomorphism classes of torsors under a sheaf of groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Filtered diagrams of groups have the colimit group constructed from their sections. -/
private instance filteredGroupColimits {I : Type (u + 1)} [SmallCategory I] [IsFiltered I] :
    HasColimitsOfShape I GrpCat.{u + 1} where
  has_colimit F := HasColimit.mk
    ⟨GrpCat.FilteredColimits.colimitCocone.{u + 1, u + 1} F,
      GrpCat.FilteredColimits.colimitCoconeIsColimit.{u + 1, u + 1} F⟩

/-- Filtered colimits of groups also exist when the indexing morphisms lie in a smaller universe. -/
private instance filteredGroupColimitsSmallHoms {I : Type (u + 1)} [Category.{u} I]
    [IsFiltered I] : HasColimitsOfShape I GrpCat.{u + 1} :=
  hasColimitsOfShape_of_equivalence (ULiftHom.equiv : I ≌ ULiftHom.{u + 1} I).symm

/-- Forgetting groups preserves filtered colimits indexed by categories with smaller morphisms. -/
private instance forgetGrp_preservesFilteredColimitsSmallHoms {I : Type (u + 1)}
    [Category.{u} I] [IsFiltered I] :
    PreservesColimitsOfShape I (CategoryTheory.forget GrpCat.{u + 1}) :=
  preservesColimitsOfShape_of_equiv
    (ULiftHom.equiv : I ≌ ULiftHom.{u + 1} I).symm _

/-- The opposite comma categories of the étale-to-pro-étale inclusion are filtered. -/
private instance (X : Scheme.{u}) (U : X.ProEtᵒᵖ) :
    IsFiltered (CostructuredArrow (etaleToProEt X).op U) :=
  IsFiltered.of_equivalence (structuredArrowOpEquivalence (etaleToProEt X) U.unop)

/-- Group-valued presheaves have pointwise left Kan extension along the inclusion of sites. -/
private instance groupPointwiseKanExtension (X : Scheme.{u})
    (F : X.Etaleᵒᵖ ⥤ GrpCat.{u + 1}) :
    (etaleToProEt X).op.HasPointwiseLeftKanExtension F :=
  fun _ ↦ inferInstance

/-- Group-valued presheaves have left Kan extension along the étale-to-pro-étale inclusion. -/
instance etaleToProEt_groupLeftKanExtension (X : Scheme.{u})
    (F : X.Etaleᵒᵖ ⥤ GrpCat.{u + 1}) :
    (etaleToProEt X).op.HasLeftKanExtension F := by infer_instance

/-- Group-valued presheaves on the small pro-étale site have left exact sheafification. -/
instance proEtale_groupHasSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) GrpCat.{u + 1} := by infer_instance

/-- Forgetting groups preserves sheafification on the small pro-étale site. -/
instance proEtale_forgetGrp_preservesSheafification (X : Scheme.{u}) :
    (ProEt.topology X).PreservesSheafification (CategoryTheory.forget GrpCat.{u + 1}) := by
  infer_instance

/-- Forgetting groups preserves left Kan extensions along the opposite comparison of sites. -/
instance etaleToProEt_forgetGrp_preservesLeftKanExtensions (X : Scheme.{u}) :
    (CategoryTheory.forget GrpCat.{u + 1}).PreservesLeftKanExtensions (etaleToProEt X).op := by
  intro F
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the left Kan extension on set-valued presheaves is a colimit over
the corresponding costructured-arrow category. -/
private def typeLanEvaluationIso (X : Scheme.{u}) (Y : X.ProEtᵒᵖ) :
    (etaleToProEt X).op.lan ⋙
      (CategoryTheory.evaluation X.ProEtᵒᵖ (Type (u + 1))).obj Y ≅
      (Functor.whiskeringLeft _ _ (Type (u + 1))).obj
        (CostructuredArrow.proj (etaleToProEt X).op Y) ⋙ colim :=
  NatIso.ofComponents (fun F =>
    (etaleToProEt X).op.leftKanExtensionObjIsoColimit F Y) (fun {F₁ F₂} φ => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      (etaleToProEt X).op F₁ Y).hom_ext
    intro T
    have h₂ := congr_app ((etaleToProEt X).op.lanUnit.naturality φ) T.left
    change φ.app T.left ≫ ((etaleToProEt X).op.leftKanExtensionUnit F₂).app T.left =
      ((etaleToProEt X).op.leftKanExtensionUnit F₁).app T.left ≫
        ((etaleToProEt X).op.lan.map φ).app ((etaleToProEt X).op.obj T.left) at h₂
    change
      (((etaleToProEt X).op.leftKanExtensionUnit F₁).app T.left ≫
        ((etaleToProEt X).op.leftKanExtension F₁).map T.hom) ≫
          (((etaleToProEt X).op.lan.map φ).app Y ≫
            ((etaleToProEt X).op.leftKanExtensionObjIsoColimit F₂ Y).hom) =
      (((etaleToProEt X).op.leftKanExtensionUnit F₁).app T.left ≫
        ((etaleToProEt X).op.leftKanExtension F₁).map T.hom) ≫
          (((etaleToProEt X).op.leftKanExtensionObjIsoColimit F₁ Y).hom ≫
            colim.map (Functor.whiskerLeft (CostructuredArrow.proj _ Y) φ))
    simp only [Category.assoc, NatTrans.naturality_assoc,
      ← reassoc_of% h₂, Functor.ι_leftKanExtensionObjIsoColimit_hom_assoc]
    change φ.app T.left ≫
        ((etaleToProEt X).op.leftKanExtensionUnit F₂).app T.left ≫
        ((etaleToProEt X).op.leftKanExtension F₂).map T.hom ≫
        ((etaleToProEt X).op.leftKanExtensionObjIsoColimit F₂ Y).hom =
      colimit.ι _ T ≫ colimMap (Functor.whiskerLeft (CostructuredArrow.proj _ Y) φ)
    rw [Functor.ι_leftKanExtensionObjIsoColimit_hom, ι_colimMap]
    rfl)


/-- Left Kan extension of set-valued presheaves along the comparison preserves finite limits. -/
private instance typeLan_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits
      ((etaleToProEt X).op.lan :
        (X.Etaleᵒᵖ ⥤ Type (u + 1)) ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1)) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
  intro I _ _
  apply preservesLimitsOfShape_of_evaluation _ I
  intro Y
  exact preservesLimitsOfShape_of_natIso (typeLanEvaluationIso X Y).symm

/-- Inverse image of sheaves of sets along the comparison of small sites is left exact. -/
instance etaleToProEtPullback_type_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (etaleToProEtPullback X (Type (u + 1))) := by
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- Inverse image induces a map from étale torsor classes to pro-étale torsor classes. -/
def etaleToProEt_torsorIsoClasses (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) :
    Torsor.IsoClasses G →
      Torsor.IsoClasses ((etaleToProEtPullback X GrpCat.{u + 1}).obj G) :=
  Torsor.pullbackIsoClasses (ProEt.topology X) (etaleToProEt X) G

/-- The étale-to-pro-étale comparison sends the class of a torsor to its inverse-image class. -/
theorem etaleToProEt_torsorIsoClasses_mk (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) (P : Torsor G) :
    etaleToProEt_torsorIsoClasses X G (_root_.Quotient.mk'' P) =
      _root_.Quotient.mk'' (Torsor.pullback (ProEt.topology X) (etaleToProEt X) G P) := rfl

/-- Inverse image from the small étale site to the small pro-étale site induces a bijection
on isomorphism classes of torsors under every sheaf of possibly noncommutative groups. -/
theorem etaleToProEt_torsorIsoClasses_bijective (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) :
    Function.Bijective (etaleToProEt_torsorIsoClasses X G) := sorry

end AlgebraicGeometry.Scheme
