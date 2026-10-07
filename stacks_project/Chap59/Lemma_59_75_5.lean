module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Remark_59_75_2_Yet_another_description_of_sp_Map

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme.Etale.Small

universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme

/-- All specialization maps of an étale sheaf of sets, after the identifications
of Remark 59.75.2, are bijective. -/
def étaleSpecializationMapsBijective {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    (F : Sheaf S.smallEtaleTopology (Type u)) : Prop :=
  ∀ (sbar tbar : GeometricPoint S) (RshS RshT : Type u)
    [CommRing RshS] [Algebra (S.presheaf.stalk sbar.image) RshS]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) RshS]
    [CommRing RshT] [Algebra (S.presheaf.stalk tbar.image) RshT]
    [IsStrictHenselizationOf (S.presheaf.stalk tbar.image) RshT]
    [HasWeakSheafify (strictHenselizationScheme S sbar RshS).smallEtaleTopology (Type u)]
    [HasWeakSheafify (strictHenselizationScheme S tbar RshT).smallEtaleTopology (Type u)]
    (c : strictHenselizationScheme S tbar RshT ⟶
      strictHenselizationScheme S sbar RshS)
    [∀ P : S.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback (strictHenselizationMap S sbar RshS)).op.HasLeftKanExtension P]
    [∀ P : S.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback (strictHenselizationMap S tbar RshT)).op.HasLeftKanExtension P]
    [∀ P : (strictHenselizationScheme S sbar RshS).Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback c).op.HasLeftKanExtension P]
    (hc_over :
      c ≫ strictHenselizationMap S sbar RshS =
        strictHenselizationMap S tbar RshT)
    (eS :
      Scheme.Etale.stalk sbar F.obj ≃
        etaleGlobalSections
          (((smallEtalePullback (strictHenselizationMap S sbar RshS)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S sbar RshS).smallEtaleTopology).obj F))
    (ePull :
      (((smallEtalePullback c).sheafPullback (Type u)
          (strictHenselizationScheme S sbar RshS).smallEtaleTopology
          (strictHenselizationScheme S tbar RshT).smallEtaleTopology).obj
          (((smallEtalePullback (strictHenselizationMap S sbar RshS)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S sbar RshS).smallEtaleTopology).obj F)).obj.obj
        (op ((smallEtalePullback c).obj
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance))) ≃
        etaleGlobalSections
          (((smallEtalePullback (strictHenselizationMap S tbar RshT)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S tbar RshT).smallEtaleTopology).obj F))
    (eT :
      Scheme.Etale.stalk tbar F.obj ≃
        etaleGlobalSections
          (((smallEtalePullback (strictHenselizationMap S tbar RshT)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S tbar RshT).smallEtaleTopology).obj F)),
    Function.Bijective (étaleSpecializationMap S sbar tbar RshS RshT c hc_over F eS ePull eT)

/-- Geometric stalks of a finite locally constant étale sheaf of sets are finite. -/
theorem IsFiniteLocallyConstant.finite_etaleStalk {S : Scheme.{u}}
    [HasFiniteIrreducibleComponentsOnCompactOpens S]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
    {F : Sheaf S.smallEtaleTopology (Type u)}
    (hF : CategoryTheory.Sheaf.IsFiniteLocallyConstant F) (sbar : GeometricPoint S) :
    Finite (Scheme.Etale.stalk sbar F.obj) := sorry

/-- Specialization maps of a finite locally constant étale sheaf of sets are bijective. -/
theorem IsFiniteLocallyConstant.bijective_étaleSpecializationMap {S : Scheme.{u}}
    [HasFiniteIrreducibleComponentsOnCompactOpens S]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
    {F : Sheaf S.smallEtaleTopology (Type u)}
    (hF : CategoryTheory.Sheaf.IsFiniteLocallyConstant F) :
    étaleSpecializationMapsBijective F := sorry

/-- Finite geometric stalks together with bijective specialization maps imply finite
local constancy, when every quasi-compact open of `S` has finitely many irreducible
components. -/
theorem isFiniteLocallyConstant_of_finiteStalks_bijectiveSpecialization
    {S : Scheme.{u}} [HasFiniteIrreducibleComponentsOnCompactOpens S]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
    (F : Sheaf S.smallEtaleTopology (Type u))
    (hFinite : ∀ sbar : GeometricPoint S, Finite (Scheme.Etale.stalk sbar F.obj))
    (hSp : étaleSpecializationMapsBijective F) :
    CategoryTheory.Sheaf.IsFiniteLocallyConstant F := sorry

/-- Lemma 59.75.5: on a scheme whose quasi-compact opens have finitely many
irreducible components (for example if the underlying space is Noetherian, or if
the scheme is locally Noetherian), a sheaf of sets on the small étale site is
finite locally constant if and only if every geometric stalk is finite and every
specialization map `sp : F_s̄ → F_t̄` is bijective. -/
@[stacks 0GJ7]
theorem finiteLocallyConstant_iff_finiteStalks_bijectiveSpecialization
    {S : Scheme.{u}} [HasFiniteIrreducibleComponentsOnCompactOpens S]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
    (F : Sheaf S.smallEtaleTopology (Type u)) :
    CategoryTheory.Sheaf.IsFiniteLocallyConstant F ↔
      (∀ sbar : GeometricPoint S, Finite (Scheme.Etale.stalk sbar F.obj)) ∧
        étaleSpecializationMapsBijective F := sorry

end AlgebraicGeometry.Scheme
