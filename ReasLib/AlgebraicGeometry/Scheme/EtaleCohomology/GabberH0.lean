module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Henselian
public import Mathlib.Topology.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsPullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Global sections of a small Zariski sheaf of sets at the terminal open. -/
abbrev zariskiGlobalSections {X : Scheme.{u}}
    (G : Sheaf X.smallZariskiTopology (Type (u + 1))) : Type (u + 1) :=
  G.obj.obj (op ((smallZariskiOpenFunctor X).obj ⊤))

/-- The pullback of the identity morphism along a scheme morphism is its source. -/
private def pullback_snd_idIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullback (𝟙 Y) f ≅ X where
  hom := pullback.snd (𝟙 Y) f
  inv := pullback.lift f (𝟙 X) (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      simpa only [Category.comp_id] using
        (pullback.condition (f := 𝟙 Y) (g := f)).symm
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  inv_hom_id := pullback.lift_snd _ _ _

/-- Pullback of the identity étale object is the identity étale object of the source. -/
private def smallEtalePullback_obj_id {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtalePullback f).obj (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance) ≅
      MorphismProperty.Over.mk _ (𝟙 X) inferInstance :=
  MorphismProperty.Over.isoMk (pullback_snd_idIso f) (by
    change (pullback_snd_idIso f).hom ≫ 𝟙 X = pullback.snd (𝟙 Y) f
    simp [pullback_snd_idIso])

/-- Pullback of the terminal Zariski open is the terminal open of the source. -/
private def smallZariskiPullback_obj_top {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallZariskiPullback f).obj ((smallZariskiOpenFunctor Y).obj ⊤) ≅
      (smallZariskiOpenFunctor X).obj ⊤ :=
  MorphismProperty.Over.isoMk
      (pullbackSymmetry (⊤ : Y.Opens).ι f ≪≫ pullbackRestrictIsoRestrict f ⊤) (by
        change (pullbackSymmetry (⊤ : Y.Opens).ι f).hom ≫
          (pullbackRestrictIsoRestrict f ⊤).hom ≫ (f ⁻¹ᵁ (⊤ : Y.Opens)).ι =
            pullback.snd (⊤ : Y.Opens).ι f
        rw [pullbackRestrictIsoRestrict_hom_ι, pullbackSymmetry_hom_comp_fst]) ≪≫
    (smallZariskiOpenFunctor X).mapIso (eqToIso (Opens.map_top f.base))

/-- Canonical restriction of Zariski global sections along a scheme morphism. -/
@[no_expose]
def zariskiSectionsPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallZariskiTopology (Type (u + 1))]
    [HasWeakSheafify Y.smallZariskiTopology (Type (u + 1))]
    [∀ P : Y.smallZariskiSiteᵒᵖ ⥤ Type (u + 1),
      (smallZariskiPullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallZariskiTopology (Type (u + 1))) :
    zariskiGlobalSections G →
      zariskiGlobalSections
        (((smallZariskiPullback f).sheafPullback (Type (u + 1))
            Y.smallZariskiTopology X.smallZariskiTopology).obj G) :=
  fun s ↦
    ((((smallZariskiPullback f).sheafPullback (Type (u + 1))
            Y.smallZariskiTopology X.smallZariskiTopology).obj G).obj.map
        (op (smallZariskiPullback_obj_top f).inv))
      (((smallZariskiPullback f).sheafPushforwardContinuousObjObjIso (Type (u + 1))
          (((smallZariskiPullback f).sheafPullback (Type (u + 1))
              Y.smallZariskiTopology X.smallZariskiTopology).obj G)
          ((smallZariskiOpenFunctor Y).obj ⊤)).hom
        ((((smallZariskiPullback f).sheafAdjunctionContinuous (Type (u + 1))
              Y.smallZariskiTopology X.smallZariskiTopology).unit.app G).hom.app
          (op ((smallZariskiOpenFunctor Y).obj ⊤)) s))

/-- Zariski global sections restrict bijectively along a morphism for every sheaf of sets. -/
def zariskiGlobalSections_bijective {X Z : Scheme.{u}} (i : Z ⟶ X)
    [HasWeakSheafify X.smallZariskiTopology (Type (u + 1))]
    [HasWeakSheafify Z.smallZariskiTopology (Type (u + 1))]
    [∀ P : X.smallZariskiSiteᵒᵖ ⥤ Type (u + 1),
      (smallZariskiPullback i).op.HasLeftKanExtension P] : Prop :=
  ∀ G : Sheaf X.smallZariskiTopology (Type (u + 1)),
    Function.Bijective (zariskiSectionsPullback i G)

/-- Canonical restriction of étale global sections along a scheme morphism. -/
@[no_expose]
def etaleGlobalSectionsPullback {X Z : Scheme.{u}} (i : Z ⟶ X)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasWeakSheafify Z.smallEtaleTopology (Type u)]
    [∀ P : X.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback i).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    etaleGlobalSections F →
      etaleGlobalSections ((Sheaf.smallEtaleInverseImage i (Type u)).obj F) :=
  fun s ↦
    ((Sheaf.smallEtaleInverseImage i (Type u)).obj F).obj.map
      (op (smallEtalePullback_obj_id i).inv) (etaleSectionsPullback i F s)

/-- For a closed immersion into a quasi-compact and quasi-separated scheme, bijectivity
of Zariski global-sections restriction, stable under every finite base change, implies
bijectivity of étale global-sections restriction for every sheaf of sets. -/
theorem etaleGlobalSections_bijective_of_zariskiFiniteBaseChange
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify X.smallZariskiTopology (Type (u + 1))]
    [HasWeakSheafify Z.smallZariskiTopology (Type (u + 1))]
    [∀ P : X.smallZariskiSiteᵒᵖ ⥤ Type (u + 1),
      (smallZariskiPullback i).op.HasLeftKanExtension P]
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasWeakSheafify Z.smallEtaleTopology (Type u)]
    [∀ P : X.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback i).op.HasLeftKanExtension P]
    (h_zar : zariskiGlobalSections_bijective i)
    (h_fin : ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f]
      [HasWeakSheafify X'.smallZariskiTopology (Type (u + 1))]
      [HasWeakSheafify (pullback i f).smallZariskiTopology (Type (u + 1))]
      [∀ P : X'.smallZariskiSiteᵒᵖ ⥤ Type (u + 1),
        (smallZariskiPullback (pullback.snd i f)).op.HasLeftKanExtension P],
      zariskiGlobalSections_bijective (pullback.snd i f))
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    Function.Bijective (etaleGlobalSectionsPullback i F) := sorry

/-- For a henselian pair, étale global sections restrict bijectively to the closed fiber. -/
theorem etaleGlobalSections_bijective_of_henselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    [HasWeakSheafify (Spec (CommRingCat.of A)).smallEtaleTopology (Type u)]
    [HasWeakSheafify (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology (Type u)]
    [∀ P : (Spec (CommRingCat.of A)).Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).op.HasLeftKanExtension P]
    (F : Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology (Type u)) :
    Function.Bijective
      (etaleGlobalSectionsPullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F) := sorry

end AlgebraicGeometry.Scheme

end
