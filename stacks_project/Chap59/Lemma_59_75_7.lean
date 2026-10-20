/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImageStalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization.DirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

/- Private implementation visibility justification: the typed source bridge supplies
canonical sheafification and abelian-category evidence explicitly. -/
set_option backward.privateInPublic true

universe u

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

namespace AlgebraicGeometry.Scheme.Etale

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (sbar : GeometricPoint S)
variable (RshS : Type u) [CommRing RshS]
variable [Algebra (S.presheaf.stalk sbar.image) RshS]
variable [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) RshS]
variable (tbar : GeometricPoint (strictHenselizationScheme S sbar RshS))

/-- The geometric point of `S` obtained by composing `t̄` with the
strict-henselization map `Spec(O^{sh}_{S,s̄}) ⟶ S`. -/
def imageGeometricPoint : GeometricPoint S :=
  @GeometricPoint.of _ tbar.K inferInstance tbar.isAlgClosed
    (tbar.hom ≫ strictHenselizationMap S sbar RshS)

variable (RshT : Type u) [CommRing RshT]
variable [Algebra (S.presheaf.stalk (imageGeometricPoint sbar RshS tbar).image) RshT]
variable [IsStrictHenselizationOf
  (S.presheaf.stalk (imageGeometricPoint sbar RshS tbar).image) RshT]
variable (c :
  strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT ⟶
    strictHenselizationScheme S sbar RshS)
variable (hc_over :
  c ≫ strictHenselizationMap S sbar RshS =
    strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)

/-- The fibre-product morphism `id_X × c : X ×_S Spec(O^{sh}_{S,t̄}) ⟶
X ×_S Spec(O^{sh}_{S,s̄})` over `f` and the Remark 59.75.2 comparison `c`. -/
def idXTimesC :
    henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT ⟶
      henselizedFiber f sbar RshS :=
  pullback.map f
    (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)
    f (strictHenselizationMap S sbar RshS) (𝟙 X) c (𝟙 S)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id
        (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)).trans
      hc_over.symm)

end AlgebraicGeometry.Scheme.Etale

/- Lemma 59.75.7: specialization of derived direct-image stalks commutes with pullback
on pointed strict-henselian fibers under the canonical invertible cohomology comparisons. -/
@[stacks 0GJ8] #check
  (AlgebraicGeometry.Scheme.Etale.derivedPushforward_specialization_commSq :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (s t : GeometricPoint S)
      (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
      (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
      [QuasiCompact f] [QuasiSeparated f]
      (K : @DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
        inferInstance (sectionsAbelian X) inferInstance),
      CommSq
        (Etale.derivedPushforward_specializationMap f s t point point_over
          K.obj)
        (Etale.Cohomology.etaleStalkToStrictHenselizationCohomology f s
          K.obj)
        (Etale.Cohomology.etaleStalkToStrictHenselizationCohomology f t
          K.obj)
        (Etale.strictHenselizationCohomologyPullback f s t point point_over
          K.obj) ∧
      IsIso (Etale.Cohomology.etaleStalkToStrictHenselizationCohomology f s
        K.obj) ∧
      IsIso (Etale.Cohomology.etaleStalkToStrictHenselizationCohomology f t
        K.obj))

end
