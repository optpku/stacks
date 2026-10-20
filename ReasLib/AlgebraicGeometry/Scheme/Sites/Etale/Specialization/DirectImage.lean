module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.StalkBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Comparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry

noncomputable section

/- Private implementation visibility justification: comparison types use canonical
sheafification and abelian-category evidence without exporting auxiliary infrastructure. -/
set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Abelian-group presheaves on the small étale site have canonical left-exact sheafification. -/
private abbrev sectionsSheafification (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (@instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
          T.Etale inferInstance T.smallEtaleTopology AddCommGrpCat.{u + 1} inferInstance
          (fun P U cover ↦ inferInstance) (fun U ↦ inferInstance)
          _ _ inferInstance inferInstance
          (fun U ↦ @PreservesFilteredColimitsOfSize.preserves_filtered_colimits _ _ _ _
            (CategoryTheory.forget AddCommGrpCat.{u + 1})
            AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
            (T.smallEtaleTopology.Cover U)ᵒᵖ inferInstance
            (@isFiltered_op_of_isCofiltered (T.smallEtaleTopology.Cover U) inferInstance
              (isCofiltered_of_semilatticeInf_nonempty (T.smallEtaleTopology.Cover U)))) inferInstance
          (fun {U} cover ↦ inferInstance) inferInstance inferInstance (fun U ↦ inferInstance))

/-- Abelian étale sheaves form an abelian category via left-exact sheafification. -/
private abbrev sectionsAbelian (T : Scheme.{u}) :
    CategoryTheory.Abelian (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  @sheafIsAbelian _ _ _ _ inferInstance _ (sectionsSheafification T)

/-- Derived global étale sections with canonical sheafification. -/
private abbrev globalSectionsDerived (T : Scheme.{u}) :=
  @siteAbelianSectionsDerived.{u + 1, u, u + 1} T.Etale inferInstance
    T.smallEtaleTopology (globalEtale T) (sectionsSheafification T) inferInstance

variable {X S : Scheme.{u}} (f : X ⟶ S) (s t : GeometricPoint S)
variable (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
variable (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)

/-- The pointed comparison of strict henselizations induces a map of their fibers over a
scheme morphism. -/
def strictHenselizationFiberMap :
    pullback f (StrictHenselization.toScheme S t) ⟶
      pullback f (StrictHenselization.toScheme S s) :=
  pullback.map f (StrictHenselization.toScheme S t)
    f (StrictHenselization.toScheme S s) (𝟙 X)
    (StrictHenselization.comparison s t point point_over) (𝟙 S)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id (StrictHenselization.toScheme S t)).trans
      (StrictHenselization.comparison_over s t point point_over).symm)

/-- The fiber comparison commutes with projection to the original scheme. -/
theorem strictHenselizationFiberMap_fst :
    strictHenselizationFiberMap f s t point point_over ≫
        pullback.fst f (StrictHenselization.toScheme S s) =
      pullback.fst f (StrictHenselization.toScheme S t) := sorry

/-- The second projection of the fiber comparison is the pointed strict-henselization
comparison composed with the second projection. -/
theorem strictHenselizationFiberMap_snd :
    strictHenselizationFiberMap f s t point point_over ≫
        pullback.snd f (StrictHenselization.toScheme S s) =
      pullback.snd f (StrictHenselization.toScheme S t) ≫
        StrictHenselization.comparison s t point point_over := sorry

/-- Derived cohomology pulls back along the pointed fiber comparison, with coefficients
transported by composition of inverse images. -/
def strictHenselizationCohomologyPullback
    (K : @DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      inferInstance (sectionsAbelian X) inferInstance) :
    (globalSectionsDerived (pullback f (StrictHenselization.toScheme S s))).obj
        ((Derived.inverseImage (pullback.fst f (StrictHenselization.toScheme S s))).obj K) ⟶
      (globalSectionsDerived (pullback f (StrictHenselization.toScheme S t))).obj
          ((Derived.inverseImage (pullback.fst f (StrictHenselization.toScheme S t))).obj K) :=
  (Derived.sectionsPullback (strictHenselizationFiberMap f s t point point_over)).app
      ((Derived.inverseImage (pullback.fst f (StrictHenselization.toScheme S s))).obj K) ≫
    (globalSectionsDerived (pullback f (StrictHenselization.toScheme S t))).map
      ((Derived.inverseImageCompIso (strictHenselizationFiberMap f s t point point_over)
        (pullback.fst f (StrictHenselization.toScheme S s))).inv.app K ≫
        (eqToIso (congrArg (fun morphism => (Derived.inverseImage morphism).obj K)
          (strictHenselizationFiberMap_fst f s t point point_over))).hom)

/-- Geometric specialization on the stalks of a derived direct image is the exact
localization of the geometric stalk specialization transformation. -/
def derivedPushforward_specializationMap
    (K : @DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      inferInstance (sectionsAbelian X) inferInstance) :
    (@ExactFunctor.mapDerivedCategory _ _ (sectionsAbelian S) _ _ _ _ _ (etaleStalkExact s)).obj ((Derived.directImage f).obj K) ⟶
      (@ExactFunctor.mapDerivedCategory _ _ (sectionsAbelian S) _ _ _ _ _ (etaleStalkExact t)).obj ((Derived.directImage f).obj K) :=
  (@ExactFunctor.MapDerivedCategory.map _ _ (sectionsAbelian S) _ _ _ _ _ _ _
    (ObjectProperty.homMk
    ((StrictHenselianNeighborhood.canonical s).specializationPoint
      point point_over).sheafFiber : etaleStalkExact s ⟶ etaleStalkExact t)).app
        ((Derived.directImage f).obj K)

/-- Specialization commutes with the canonical comparison from derived direct-image stalks
to strict-henselian base-change cohomology for arbitrary scheme morphisms and unbounded
étale complexes. -/
theorem derivedPushforward_specialization_leftSquare
    {X S : Scheme.{u}} (f : X ⟶ S) (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    CommSq (Cohomology.etaleStalkToStrictHenselizationCohomology f s K)
      (derivedPushforward_specializationMap f s t point point_over K)
      (strictHenselizationCohomologyPullback f s t point point_over K)
      (Cohomology.etaleStalkToStrictHenselizationCohomology f t K) := sorry

/-- For a quasi-compact quasi-separated morphism and bounded-below coefficients, geometric
specialization commutes with pullback on strict-henselian fibers through the canonical
invertible stalk-to-cohomology maps. -/
theorem derivedPushforward_specialization_commSq [QuasiCompact f] [QuasiSeparated f]
    (K : @DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      inferInstance (sectionsAbelian X) inferInstance) :
    CommSq
      (derivedPushforward_specializationMap f s t point point_over K.obj)
      (Cohomology.etaleStalkToStrictHenselizationCohomology f s K.obj)
      (Cohomology.etaleStalkToStrictHenselizationCohomology f t K.obj)
      (strictHenselizationCohomologyPullback f s t point point_over K.obj) ∧
    IsIso (Cohomology.etaleStalkToStrictHenselizationCohomology f s
      K.obj) ∧
    IsIso (Cohomology.etaleStalkToStrictHenselizationCohomology f t
      K.obj) := sorry

/-- A morphism completing the geometric-fiber cohomology square need not exist, even for
quasi-compact quasi-separated scheme morphisms and bounded-below étale complexes. -/
theorem not_forall_exists_fiberSpecialization :
    ¬ ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
      (s t : GeometricPoint S)
      (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
      (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      ∃ φ, CommSq (Cohomology.strictHenselizationToGeometricFiberCohomology f s K.obj)
        (strictHenselizationCohomologyPullback f s t point point_over K.obj) φ
        (Cohomology.strictHenselizationToGeometricFiberCohomology f t K.obj) := sorry

end AlgebraicGeometry.Scheme.Etale

end
