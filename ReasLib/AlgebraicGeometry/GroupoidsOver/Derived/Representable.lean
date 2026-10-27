/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.ChaoticPullback
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.SiteComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.Small
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SmallEtaleComparison

/-!
# Derived quasi-coherent comparison for representable groupoid fibrations

A representing equivalence restricts to affine sites and induces a ringed-topos
comparison. Its derived inverse image identifies the quasi-coherent category
with sectionwise small cohomology with the native derived quasi-coherent category
of the representing algebraic space.
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

/-- The restriction of the representing small étale comparison to affine objects. -/
def affineSiteFunctor :
    AlgebraicSpace.affineEtaleSite F ⥤ affineSite X :=
  FullSubcategory.restrict (smallEtaleFunctor F X e) (affineEtale_mapsTo F X e)

/-- On underlying étale objects, `affineSiteFunctor` is `smallEtaleFunctor`. -/
theorem affineSiteFunctor_obj (U : AlgebraicSpace.affineEtaleSite F) :
    ((affineSiteFunctor F X e).obj U).obj = (smallEtaleFunctor F X e).obj U.obj :=
  rfl

/-- Restricting the representing comparison to affine objects commutes with
the inclusions into the small étale and total sites. -/
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

/-- Restriction along the affine representing comparison has pointwise right
Kan extensions for presheaves in the coefficient universe. -/
instance affineSiteFunctorHasPointwiseRightKanExtension
    (P : (AlgebraicSpace.affineEtaleSite F)ᵒᵖ ⥤ Type (u + 1)) :
    (affineSiteFunctor F X e).op.HasPointwiseRightKanExtension P := sorry

/-- The morphism of chaotic ringed topoi induced by `affineSiteFunctor` and the
realization map on global sections. -/
def affineComparisonToposHom :
    RingedSite.ToposHom.{u + 1, u, u + 1, u, u + 1}
      (AlgebraicSpace.DerivedQCoh.affineChaoticRingedSite F) (affineRingedSite X) :=
  RingedSite.Cocontinuous.toRingedTopos.{u + 1, u, u + 1, u, u + 1}
    (X := AlgebraicSpace.DerivedQCoh.affineChaoticRingedSite F) (Y := affineRingedSite X)
    (affineSiteFunctor F X e) (affineStructureSheafPresheafMap F X e)

/-- Scalar restriction along the affine structure map is a right adjoint. -/
theorem affineComparisonRestrictScalarsIsRightAdjoint :
    (SheafOfModules.restrictScalars.{u + 1}
      (affineComparisonToposHom F X e).structureMap).IsRightAdjoint := sorry

/-- Module pullback along the affine comparison, from the homotopy category
of modules to the derived category of modules. -/
def affineModulePullbackToDerived :
    RingedSite.Hom.ModuleHomotopy.{u + 1} (affineRingedSite X) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1}
        (AlgebraicSpace.DerivedQCoh.affineChaoticRingedSite F) :=
  @RingedSite.ToposHom.modulePullbackToDerived.{u + 1, u, u + 1, u, u + 1}
    _ _ inferInstance inferInstance
    (affineComparisonToposHom F X e) inferInstance inferInstance
    (affineComparisonRestrictScalarsIsRightAdjoint F X e)

/-- The affine representing comparison admits unbounded derived module pullback. -/
theorem affineComparisonHasModulePullbackDerived :
    (affineModulePullbackToDerived F X e).HasLeftDerivedFunctor
      (RingedSite.Hom.ModuleQis.{u + 1} (affineRingedSite X)) := sorry

/-- The total left derived module pullback along the affine representing comparison. -/
def affineDerivedPullback :
    RingedSite.Hom.ModuleDerived.{u + 1} (affineRingedSite X) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1}
        (AlgebraicSpace.DerivedQCoh.affineChaoticRingedSite F) :=
  @Functor.totalLeftDerived _ _ _ inferInstance inferInstance inferInstance
    (affineModulePullbackToDerived F X e)
    (RingedSite.Hom.moduleLocalization.{u + 1} (affineRingedSite X))
    (RingedSite.Hom.ModuleQis.{u + 1} (affineRingedSite X)) inferInstance
    (affineComparisonHasModulePullbackDerived F X e)

/-- Derived affine pullback preserves comparison-map quasi-coherence and
sectionwise small cohomology. -/
theorem toAffineQC_mapsTo :
    smallQCProperty X ≤
      (AlgebraicSpace.DerivedQCoh.affineQCProperty F).inverseImage
        (affineDerivedPullback F X e) :=
  sorry

/-- Derived inverse image along the affine comparison, restricted to
quasi-coherent objects with sectionwise small cohomology. -/
def toAffineQC :
    SmallQC X ⥤ AlgebraicSpace.DerivedQCoh.AffineQC F :=
  FullSubcategory.restrict
    (affineDerivedPullback F X e) (toAffineQC_mapsTo F X e)

/-- The underlying derived module of `toAffineQC` is chaotic derived pullback. -/
theorem toAffineQC_obj (K : SmallQC X) :
    ((toAffineQC F X e).obj K).obj =
      (affineDerivedPullback F X e).obj K.obj :=
  rfl

/-- Pointwise existence of derived inverse image along the affine comparison. -/
theorem derivedPullback_hasPointwise :
    (affineModulePullbackToDerived F X e).HasPointwiseLeftDerivedFunctor
      (RingedSite.Hom.ModuleQis.{u + 1} (affineRingedSite X)) :=
  sorry

/-- The homotopy-to-derived affine module pullback commutes with integer shifts. -/
@[implicit_reducible]
def affinePullbackToDerived_commShift :
    (affineModulePullbackToDerived F X e).CommShift ℤ := by
  let pullback := @RingedSite.ToposHom.modulePullback.{u + 1, u, u + 1, u, u + 1} _ _ inferInstance inferInstance
    (affineComparisonToposHom F X e) (affineComparisonRestrictScalarsIsRightAdjoint F X e)
  -- Local instance justification (defeq pin): use additivity of this specified module pullback in its degreewise homotopy construction.
  letI := @RingedSite.ToposHom.modulePullback_additive.{u + 1, u, u + 1, u, u + 1} _ _ inferInstance inferInstance
    (affineComparisonToposHom F X e) (affineComparisonRestrictScalarsIsRightAdjoint F X e)
  change ((pullback.mapHomotopyCategory
    (ComplexShape.up ℤ)) ⋙ RingedSite.Hom.moduleLocalization.{u + 1}
      (AlgebraicSpace.DerivedQCoh.affineChaoticRingedSite F)).CommShift ℤ
  infer_instance

/-- Derived inverse image along the affine comparison commutes with shifts. -/
@[implicit_reducible]
noncomputable def derivedPullback_commShift :
    (affineDerivedPullback F X e).CommShift ℤ :=
  @Functor.totalLeftDerived_commShift _ _ _ inferInstance inferInstance inferInstance
    (affineModulePullbackToDerived F X e)
    (RingedSite.Hom.ModuleQis.{u + 1} (affineRingedSite X))
    (RingedSite.Hom.moduleLocalization.{u + 1} (affineRingedSite X))
    inferInstance inferInstance inferInstance (affinePullbackToDerived_commShift F X e)
    inferInstance inferInstance (derivedPullback_hasPointwise F X e)

/-- `toAffineQC` commutes with integer shifts, by restriction of derived pullback. -/
@[implicit_reducible]
def toAffineQC_commShift : (toAffineQC F X e).CommShift ℤ :=
  @Functor.CommShift.ofComp _ _ _ _ _ _ _ _ _
    (FullSubcategory.restrict.compιIso
      (affineDerivedPullback F X e) (toAffineQC_mapsTo F X e))
    inferInstance inferInstance ℤ
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Functor.CommShift.comp _ _ _ _ _ _ (smallQCProperty X).ι
      (affineDerivedPullback F X e) ℤ
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (derivedPullback_commShift F X e))

/-- `toAffineQC` is a triangulated functor. -/
theorem toAffineQC_isTriangulated :
    (toAffineQC F X e).IsTriangulatedWith (toAffineQC_commShift F X e) := sorry

/-- `toAffineQC` is `ℤ`-linear. -/
instance toAffineQC_linear : (toAffineQC F X e).Linear ℤ :=
  sorry

/-- `toAffineQC` is an equivalence of categories. -/
instance toAffineQC_isEquivalence : (toAffineQC F X e).IsEquivalence :=
  sorry

/-- The canonical integer-linear triangulated equivalence between the small
quasi-coherent categories on the two chaotic affine sites. -/
def toAffineQCEquivalence :
    RLinear.TriangulatedEquivalence ℤ (SmallQC X)
      (AlgebraicSpace.DerivedQCoh.AffineQC F) :=
  @RLinear.TriangulatedEquivalence.ofFunctor ℤ inferInstance _ _
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance
    (toAffineQC F X e) (toAffineQC_isEquivalence F X e)
    (toAffineQC_commShift F X e) (toAffineQC_isTriangulated F X e)
    (toAffineQC_linear F X e)

/-- The forward functor of `toAffineQCEquivalence` is `toAffineQC`. -/
theorem toAffineQCEquivalence_functor :
    (toAffineQCEquivalence F X e).functor = toAffineQC F X e :=
  rfl

/-- The canonical comparison to the native derived quasi-coherent category,
obtained by affine derived pullback and the affine presentation equivalences. -/
def toDerivedQCoh :
    SmallQC X ⥤ AlgebraicSpace.DerivedQCoh F :=
  toAffineQC F X e ⋙ AlgebraicSpace.DerivedQCoh.fromAffineQC F ⋙
    AlgebraicSpace.DerivedQCoh.affinePullback F ⋙
      AlgebraicSpace.DerivedQCoh.fromAffineEtale F

/-- The comparison acts on objects by affine derived pullback followed by the
three affine presentation comparisons. -/
theorem toDerivedQCoh_obj (K : SmallQC X) :
    (toDerivedQCoh F X e).obj K =
      (AlgebraicSpace.DerivedQCoh.fromAffineEtale F).obj
        ((AlgebraicSpace.DerivedQCoh.affinePullback F).obj
          ((AlgebraicSpace.DerivedQCoh.fromAffineQC F).obj ((toAffineQC F X e).obj K))) :=
  rfl

/-- `toDerivedQCoh` is an equivalence of categories. -/
instance toDerivedQCoh_isEquivalence : (toDerivedQCoh F X e).IsEquivalence :=
  sorry

/-- A representing algebraic space identifies the small quasi-coherent derived
category of a groupoid fibration with its native derived quasi-coherent category. -/
def qcEquivalence :
    RLinear.TriangulatedEquivalence ℤ (SmallQC X) (AlgebraicSpace.DerivedQCoh F) :=
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

/-- The inverse comparison is the composite of the affine presentation
functors and the inverse affine quasi-coherent comparison. -/
theorem qcEquivalence_inverse :
    (qcEquivalence F X e).inverse =
      (AlgebraicSpace.DerivedQCoh.affineEtaleEquivalence F).functor ⋙
        (AlgebraicSpace.DerivedQCoh.affineTopologyEquivalence F).functor ⋙
          (AlgebraicSpace.DerivedQCoh.affineQCEquivalence F).functor ⋙
            (toAffineQCEquivalence F X e).inverse :=
  rfl

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The small quasi-coherent derived category of the groupoid fibration represented
by an algebraic space is canonically equivalent to its derived quasi-coherent category. -/
def affineGroupoidsEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RLinear.TriangulatedEquivalence ℤ (GroupoidsOver.SmallQC X.toGroupoids)
      (AlgebraicSpace.DerivedQCoh X) :=
  GroupoidsOver.qcEquivalence X X.toGroupoids (Bicategory.Equivalence.id X.toGroupoids)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
