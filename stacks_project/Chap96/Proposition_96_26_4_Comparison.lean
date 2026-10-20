module

public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.ChaoticPullback
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import stacks_project.Chap75.Lemma_75_30_1_SiteComparison
public import stacks_project.Chap96.Definition_96_26_1_QC
public import stacks_project.Chap96.Lemma_96_10_1_Comparison

/-!
# Affine comparison of `QC(𝒳)` with `D_QCoh(𝒪_X)`

A bicategorical equivalence `e : F.toGroupoids ≌ X` restricts the small étale
comparison `u` of Lemma 96.10.1 to affine objects. Compatibility of structure
sheaves produces the derived inverse image
`G : QC(𝒳) ⥤ QC(X_affine, 𝒪)`, and Lemma 75.30.1 identifies the target with
`D_QCoh(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty Opposite
open CategoryTheory.ModulesOnCategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (F : AlgebraicSpace S) (X : GroupoidsOver S)
variable (e : F.toGroupoids ≌ X)

/-- Affine étale objects of `F` are sent by `smallEtaleFunctor` to objects of `X`
lying over affine schemes. -/
theorem affineEtale_mapsTo :
    AlgebraicSpace.affineEtaleObjects F ≤
      (affineObjects X).inverseImage (smallEtaleFunctor F X e) :=
  sorry

/-- The functor `X_affine ⥤ 𝒳_affine` obtained by restricting the small étale
comparison `u` of Lemma 96.10.1 to affine objects. -/
def affineSiteFunctor :
    AlgebraicSpace.affineEtaleSite F ⥤ affineSite X :=
  FullSubcategory.restrict (smallEtaleFunctor F X e) (affineEtale_mapsTo F X e)

/-- On underlying étale objects, `affineSiteFunctor` is `smallEtaleFunctor`. -/
theorem affineSiteFunctor_obj (U : AlgebraicSpace.affineEtaleSite F) :
    ((affineSiteFunctor F X e).obj U).obj = (smallEtaleFunctor F X e).obj U.obj :=
  rfl

/-- Restricting `u` to affine objects commutes with the affine inclusions. -/
theorem affineSiteFunctor_comp_inclusion :
    affineSiteFunctor F X e ⋙ affineInclusion X =
      AlgebraicSpace.affineEtaleInclusion F ⋙ smallEtaleFunctor F X e :=
  rfl

/-- Realization of `affineSiteFunctor` on schemes over `S`. -/
def affineSiteFunctor_toOver :
    affineSiteFunctor F X e ⋙ affineToOver X ≅
      AlgebraicSpace.affineEtaleInclusion F ⋙ AlgebraicSpace.smallEtaleToOver F :=
  Functor.isoWhiskerRight
      (FullSubcategory.restrict.compιIso (smallEtaleFunctor F X e)
        (affineEtale_mapsTo F X e))
      X.p ≪≫
    Functor.isoWhiskerLeft (AlgebraicSpace.affineEtaleInclusion F)
      (smallEtaleFunctor_p F X e)

/-- Scheme-valued realization of `affineSiteFunctor`. -/
def affineSiteFunctor_toScheme :
    affineSiteFunctor F X e ⋙ affineToOver X ⋙ Over.forget S ≅
      AlgebraicSpace.affineEtaleToScheme F :=
  Functor.isoWhiskerRight (affineSiteFunctor_toOver F X e) (Over.forget S)

/-- The chaotic affine ringed site of a category fibred in groupoids. -/
abbrev affineRingedSite (Y : GroupoidsOver S) : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommRingSheaf.{u + 1, u, u + 1} ⊥ (affineStructureSheaf Y)

/-- `affineRingedSite Y` is the commutative presentation of `𝒴_affine` with the
chaotic topology. -/
theorem affineRingedSite_eq (Y : GroupoidsOver S) :
    affineRingedSite Y =
      RingedSite.ofCommRingSheaf.{u + 1, u, u + 1} ⊥ (affineStructureSheaf Y) :=
  rfl

/-- The structure-presheaf map of `affineSiteFunctor`, obtained by transporting
universe-lifted global sections along the realization isomorphism. -/
def affineStructureSheafPresheafMap :
    (affineSiteFunctor F X e).op ⋙ (affineRingedSite X).structureSheaf.obj ⟶
      (AlgebraicSpace.DerivedQCoh.affineChaoticRingedSite F).structureSheaf.obj where
  app U :=
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (CommRingCat.universeLift.{u, u + 1}.map
        ((affineSiteFunctor_toScheme F X e).inv.app U.unop).appTop)
  naturality := sorry

/-- `affineSiteFunctor` as a functor of chaotic affine ringed sites. -/
def affineSiteFunctor_ringed :
    AlgebraicSpace.DerivedQCoh.affineChaoticRingedSite F ⥤ affineRingedSite X :=
  affineSiteFunctor F X e

/-- `affineSiteFunctor_ringed` is `affineSiteFunctor`. -/
theorem affineSiteFunctor_ringed_eq :
    affineSiteFunctor_ringed F X e = affineSiteFunctor F X e :=
  rfl

variable [∀ P : (AlgebraicSpace.affineEtaleSite F)ᵒᵖ ⥤ Type (u + 1),
    (affineSiteFunctor F X e).op.HasPointwiseRightKanExtension P]

/-- The morphism of chaotic ringed topoi induced by `affineSiteFunctor` and the
realization map on global sections. -/
def affineComparisonToposHom :
    RingedSite.ToposHom.{u + 1, u, u + 1, u, u + 1}
      (AlgebraicSpace.DerivedQCoh.affineChaoticRingedSite F) (affineRingedSite X) :=
  RingedSite.Cocontinuous.toRingedTopos.{u + 1, u, u + 1, u, u + 1}
    (affineSiteFunctor_ringed F X e) (affineStructureSheafPresheafMap F X e)

/-- Structure-sheaf compatibility `g♯` of the affine comparison functor. -/
def affineStructureSheafMap :=
  (affineComparisonToposHom F X e).structureMap

omit [∀ P : (AlgebraicSpace.affineEtaleSite F)ᵒᵖ ⥤ Type (u + 1),
    (affineSiteFunctor F X e).op.HasPointwiseRightKanExtension P] in
/-- `affineStructureSheafMap` is the structure map of `affineComparisonToposHom`. -/
theorem affineStructureSheafMap_eq :
    affineStructureSheafMap F X e = (affineComparisonToposHom F X e).structureMap :=
  rfl

variable [(SheafOfModules.restrictScalars.{u + 1}
    (affineComparisonToposHom F X e).structureMap).IsRightAdjoint]
variable [(affineComparisonToposHom F X e).HasModulePullbackDerived]

/-- Derived inverse image along the affine comparison carries `QC(𝒳)` into
`QC(X_affine, 𝒪)`. -/
theorem toAffineQC_mapsTo :
    qcProperty X ≤
      (AlgebraicSpace.DerivedQCoh.affineQCProperty F).inverseImage
        (affineComparisonToposHom F X e).modulePullbackDerived :=
  sorry

/-- The functor `G : QC(𝒳) ⥤ QC(X_affine, 𝒪)` of the proof of
Proposition 96.26.4, as derived inverse image along the affine comparison. -/
def toAffineQC :
    QC X ⥤ AlgebraicSpace.DerivedQCoh.AffineQC F :=
  FullSubcategory.restrict
    (affineComparisonToposHom F X e).modulePullbackDerived (toAffineQC_mapsTo F X e)

/-- The underlying derived module of `toAffineQC` is chaotic derived pullback. -/
theorem toAffineQC_obj (K : QC X) :
    ((toAffineQC F X e).obj K).obj =
      ((affineComparisonToposHom F X e).modulePullbackDerived).obj K.obj :=
  rfl

/-- Pointwise existence of derived inverse image along the affine comparison. -/
theorem derivedPullback_hasPointwise :
    ((affineComparisonToposHom F X e).modulePullbackToDerived).HasPointwiseLeftDerivedFunctor
      (RingedSite.Hom.ModuleQis.{u + 1} (affineRingedSite X)) :=
  sorry

/-- Derived inverse image along the affine comparison commutes with shifts. -/
instance affinePullbackToDerived_commShift :
    ((affineComparisonToposHom F X e).modulePullbackToDerived).CommShift ℤ := by
  -- Local instance justification (defeq pin): use additivity of this specified module pullback in its degreewise homotopy construction.
  letI := RingedSite.ToposHom.modulePullback_additive (affineComparisonToposHom F X e)
  change (((affineComparisonToposHom F X e).modulePullback.mapHomotopyCategory
    (ComplexShape.up ℤ)) ⋙ RingedSite.Hom.moduleLocalization.{u + 1}
      (AlgebraicSpace.DerivedQCoh.affineChaoticRingedSite F)).CommShift ℤ
  infer_instance

/-- Derived inverse image along the affine comparison commutes with shifts. -/
@[implicit_reducible]
noncomputable def derivedPullback_commShift :
    ((affineComparisonToposHom F X e).modulePullbackDerived).CommShift ℤ :=
  @Functor.totalLeftDerived_commShift _ _ _ inferInstance inferInstance inferInstance
    (RingedSite.ToposHom.modulePullbackToDerived (affineComparisonToposHom F X e))
    (RingedSite.Hom.ModuleQis.{u + 1} (affineRingedSite X))
    (RingedSite.Hom.moduleLocalization.{u + 1} (affineRingedSite X))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (derivedPullback_hasPointwise F X e)

/-- `toAffineQC` commutes with integer shifts, by restriction of derived pullback. -/
instance toAffineQC_commShift : (toAffineQC F X e).CommShift ℤ :=
  @Functor.CommShift.ofComp _ _ _ _ _ _ _ _ _
    (FullSubcategory.restrict.compιIso
      (affineComparisonToposHom F X e).modulePullbackDerived (toAffineQC_mapsTo F X e))
    inferInstance inferInstance ℤ
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Functor.CommShift.comp _ _ _ _ _ _ (qcProperty X).ι
      (affineComparisonToposHom F X e).modulePullbackDerived ℤ
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (derivedPullback_commShift F X e))

/-- `toAffineQC` is a triangulated functor. -/
instance toAffineQC_isTriangulated : (toAffineQC F X e).IsTriangulated :=
  sorry

/-- `toAffineQC` is `ℤ`-linear. -/
instance toAffineQC_linear : (toAffineQC F X e).Linear ℤ :=
  sorry

/-- `toAffineQC` is an equivalence of categories. -/
instance toAffineQC_isEquivalence : (toAffineQC F X e).IsEquivalence :=
  sorry

/-- The canonical `ℤ`-linear triangulated equivalence `QC(𝒳) ≌ QC(X_affine, 𝒪)`. -/
def toAffineQCEquivalence :
    RLinear.TriangulatedEquivalence ℤ (QC X)
      (AlgebraicSpace.DerivedQCoh.AffineQC F) :=
  RLinear.TriangulatedEquivalence.ofFunctor ℤ (toAffineQC F X e) inferInstance

/-- The forward functor of `toAffineQCEquivalence` is `toAffineQC`. -/
theorem toAffineQCEquivalence_functor :
    (toAffineQCEquivalence F X e).functor = toAffineQC F X e :=
  rfl

/-- The canonical comparison `QC(𝒳) ⥤ D_QCoh(𝒪_X)`, as `G` followed by the
identifications of Lemma 75.30.1. -/
def toDerivedQCoh :
    QC X ⥤ AlgebraicSpace.DerivedQCoh F :=
  toAffineQC F X e ⋙ AlgebraicSpace.DerivedQCoh.fromAffineQC F ⋙
    AlgebraicSpace.DerivedQCoh.affinePullback F ⋙
      AlgebraicSpace.DerivedQCoh.fromAffineEtale F

/-- `toDerivedQCoh` is `toAffineQC` composed with the 75.30.1 identifications. -/
theorem toDerivedQCoh_eq :
    toDerivedQCoh F X e =
      toAffineQC F X e ⋙ AlgebraicSpace.DerivedQCoh.fromAffineQC F ⋙
        AlgebraicSpace.DerivedQCoh.affinePullback F ⋙
          AlgebraicSpace.DerivedQCoh.fromAffineEtale F :=
  rfl

/-- The object map of `toDerivedQCoh` is the 75.30.1 composite applied after `toAffineQC`. -/
theorem toDerivedQCoh_obj (K : QC X) :
    (toDerivedQCoh F X e).obj K =
      (AlgebraicSpace.DerivedQCoh.fromAffineEtale F).obj
        ((AlgebraicSpace.DerivedQCoh.affinePullback F).obj
          ((AlgebraicSpace.DerivedQCoh.fromAffineQC F).obj ((toAffineQC F X e).obj K))) :=
  rfl

/-- `toDerivedQCoh` is an equivalence of categories. -/
instance toDerivedQCoh_isEquivalence : (toDerivedQCoh F X e).IsEquivalence :=
  sorry

/-- The canonical `ℤ`-linear triangulated equivalence `QC(𝒳) ≌ D_QCoh(𝒪_X)`. -/
def qcEquivalence :
    RLinear.TriangulatedEquivalence ℤ (QC X) (AlgebraicSpace.DerivedQCoh F) :=
  RLinear.TriangulatedEquivalence.trans ℤ (toAffineQCEquivalence F X e)
    (RLinear.TriangulatedEquivalence.trans ℤ
      (RLinear.TriangulatedEquivalence.symm ℤ
        (AlgebraicSpace.DerivedQCoh.affineQCEquivalence F))
      (RLinear.TriangulatedEquivalence.trans ℤ
        (RLinear.TriangulatedEquivalence.symm ℤ
          (AlgebraicSpace.DerivedQCoh.affineTopologyEquivalence F))
        (RLinear.TriangulatedEquivalence.symm ℤ
          (AlgebraicSpace.DerivedQCoh.affineEtaleEquivalence F))))

/-- The forward functor of `qcEquivalence` is `toDerivedQCoh`. -/
@[simp]
theorem qcEquivalence_functor :
    (qcEquivalence F X e).functor = toDerivedQCoh F X e :=
  rfl

/-- The inverse functor of `qcEquivalence` is the quasi-inverse packaged by the
composite of Lemma 75.30.1 with `toAffineQC`. -/
theorem qcEquivalence_inverse :
    (qcEquivalence F X e).inverse =
      (AlgebraicSpace.DerivedQCoh.affineEtaleEquivalence F).functor ⋙
        (AlgebraicSpace.DerivedQCoh.affineTopologyEquivalence F).functor ⋙
          (AlgebraicSpace.DerivedQCoh.affineQCEquivalence F).functor ⋙
            (toAffineQCEquivalence F X e).inverse :=
  rfl

end AlgebraicGeometry.GroupoidsOver
