module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.KFlat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.SiteModels

/-!
# Canonical triangulated equivalences among affine presentations of `D_QCoh`

The universe-lift comparison from `DerivedQCoh X` combines with canonical
`RLinear.TriangulatedEquivalence ℤ` functors given by restriction along the
affine étale inclusion, derived pushforward/pullback for
the étale-to-chaotic topology change, and the identity-on-ambient comparison
with `QC(X_affine, 𝒪_X)`.

All enlarged presentations require sectionwise `u`-small cohomology, so these
equivalences preserve the effective module universe of the native category.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite
open RingedSite.Hom
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The objectwise universe-lift functor from ordinary modules on `X` to the
lifted small étale presentation. -/
noncomputable def modulesLift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Modules X ⥤ RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) where
  obj := liftModule
  map := liftModuleMap
  map_id := sorry
  map_comp := sorry

/-- Universe lifting of modules is additive. -/
instance modulesLift_additive {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (modulesLift X).Additive := sorry

/-- Universe lifting of modules preserves finite limits. -/
instance modulesLift_preservesFiniteLimits {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Limits.PreservesFiniteLimits (modulesLift X) := sorry

/-- Universe lifting of modules preserves finite colimits. -/
instance modulesLift_preservesFiniteColimits {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Limits.PreservesFiniteColimits (modulesLift X) := sorry

/-- The object map of `modulesLift` is `liftModule`. -/
theorem modulesLift_obj {S : Scheme.{u}} {X : AlgebraicSpace S} (M : Modules X) :
    (modulesLift X).obj M = liftModule M := sorry

/-- The derived objectwise universe lift from ordinary modules on `X` to the lifted
small étale presentation. -/
noncomputable abbrev modulesLiftDerived {S : Scheme.{u}} (X : AlgebraicSpace S) :
    DerivedCategory (Modules X) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1} (commRingedSiteLift X) :=
  @Functor.mapDerivedCategory
    (Modules X) inferInstance inferInstance inferInstance
    (RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X))
    inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (commRingedSiteLift X))
    (modulesLift X) inferInstance inferInstance inferInstance

/-- Derived universe lifting sends quasi-coherent cohomology to quasi-coherent,
sectionwise `u`-small cohomology. -/
theorem toLifted_mapsTo {S : Scheme.{u}} (X : AlgebraicSpace S) :
    derivedQuasiCoherentModuleProperty X ≤
      (liftedProperty X).inverseImage (modulesLiftDerived X) := sorry

/-- The canonical universe-lift comparison from `DerivedQCoh X` to its lifted small
étale presentation. -/
noncomputable def toLifted {S : Scheme.{u}} (X : AlgebraicSpace S) :
    DerivedQCoh X ⥤ Lifted X :=
  FullSubcategory.restrict (modulesLiftDerived X) (toLifted_mapsTo X)

/-- The universe-lift comparison from `DerivedQCoh X` is an equivalence. -/
instance toLiftedIsEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (toLifted X).IsEquivalence := sorry

/-- The reverse universe transport from the lifted small étale presentation to
`DerivedQCoh X`. -/
noncomputable def fromLifted {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Lifted X ⥤ DerivedQCoh X where
  obj K := (toLifted X).objPreimage K
  map {K L} f :=
    (toLifted X).preimage
      (((toLifted X).objObjPreimageIso K).hom ≫ f ≫
        ((toLifted X).objObjPreimageIso L).inv)
  map_id := sorry
  map_comp := sorry

/-- Universe lifting is left adjoint to the explicit reverse universe transport. -/
noncomputable def liftedAdjunction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    toLifted X ⊣ fromLifted X where
  unit :=
    { app := fun K ↦
        ((toLifted X).preimageIso
          ((toLifted X).objObjPreimageIso ((toLifted X).obj K))).inv
      naturality := sorry }
  counit :=
    { app := fun K ↦ ((toLifted X).objObjPreimageIso K).hom
      naturality := sorry }
  left_triangle_components := sorry
  right_triangle_components := sorry

/-- The universe-lift comparison from `DerivedQCoh X` commutes with shifts. -/
instance toLiftedCommShift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (toLifted X).CommShift ℤ :=
  Functor.CommShift.ofComp
    (FullSubcategory.restrict.compιIso (modulesLiftDerived X) (toLifted_mapsTo X)) ℤ

/-- The universe-lift comparison from `DerivedQCoh X` is triangulated. -/
instance toLiftedIsTriangulated {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (toLifted X).IsTriangulated := sorry

/-- The universe-lift comparison from `DerivedQCoh X` is `ℤ`-linear. -/
instance toLiftedLinear {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (toLifted X).Linear ℤ := sorry

/-- The canonical linear triangulated equivalence between `DerivedQCoh X` and its
lifted small étale presentation. -/
noncomputable def liftedEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RLinear.TriangulatedEquivalence ℤ (DerivedQCoh X) (Lifted X) :=
  RLinear.TriangulatedEquivalence.ofAdjunction ℤ
    (liftedAdjunction X) (toLiftedIsEquivalence X)

/-- Affine étale module pushforward has its canonical inverse-image left adjoint. -/
instance affineEtaleModulePushforwardIsRightAdjoint {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ((affineEtaleRingedSiteHom X).modulePushforward.{u + 1}).IsRightAdjoint := sorry

/-- Affine-topology module pushforward has its canonical inverse-image left adjoint. -/
instance affineTopologyModulePushforwardIsRightAdjoint {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ((affineTopologyRingedSiteHom X).modulePushforward.{u + 1}).IsRightAdjoint := sorry

/-- Affine étale module pushforward admits its canonical total right-derived functor. -/
instance affineEtaleModulePushforwardHasRightDerivedFunctor {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (modulePushforwardToDerived.{u + 1}
      (affineEtaleRingedSiteHom X)).HasRightDerivedFunctor
        (ModuleQis.{u + 1} (commRingedSiteLift X)) := sorry

/-- Affine-topology module pushforward admits its canonical total right-derived functor. -/
instance affineTopologyModulePushforwardHasRightDerivedFunctor {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (modulePushforwardToDerived.{u + 1}
      (affineTopologyRingedSiteHom X)).HasRightDerivedFunctor
        (ModuleQis.{u + 1} (affineEtaleRingedSiteLift X)) := sorry

section AffineEtalePullbackWitnesses

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Derived pullback along the affine étale inclusion exists by the canonical
K-flat construction. -/
instance affineEtaleModulePullbackHasLeftDerivedFunctor :
    (@modulePullbackToDerived.{u + 1} _ _ (affineEtaleRingedSiteHom X)
      inferInstance (affineEtaleModulePushforwardIsRightAdjoint X)).HasLeftDerivedFunctor
        (ModuleQis.{u + 1} (affineEtaleRingedSiteLift X)) := sorry

/-- Derived pullback from the affine étale site exists pointwise. -/
instance affineEtaleModulePullbackHasPointwiseLeftDerivedFunctor :
    (@modulePullbackToDerived.{u + 1} _ _ (affineEtaleRingedSiteHom X)
      inferInstance
      (affineEtaleModulePushforwardIsRightAdjoint X)).HasPointwiseLeftDerivedFunctor
        (ModuleQis.{u + 1} (affineEtaleRingedSiteLift X)) := sorry

/-- Derived pullback from the affine étale site carries its canonical shift comparison. -/
@[implicit_reducible]
noncomputable def affineEtaleModulePullbackCommShift :
    (@modulePullbackDerived.{u + 1} _ _ (affineEtaleRingedSiteHom X)
      inferInstance inferInstance (affineEtaleModulePushforwardIsRightAdjoint X)
      (affineEtaleModulePullbackHasLeftDerivedFunctor X)).CommShift ℤ :=
  @Functor.totalLeftDerived_commShift _ _ _ inferInstance inferInstance inferInstance
    (@modulePullbackToDerived.{u + 1} _ _ (affineEtaleRingedSiteHom X)
      inferInstance (affineEtaleModulePushforwardIsRightAdjoint X))
    (ModuleQis.{u + 1} (affineEtaleRingedSiteLift X))
    (moduleLocalization.{u + 1} (affineEtaleRingedSiteLift X))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (affineEtaleModulePullbackHasPointwiseLeftDerivedFunctor X)

end AffineEtalePullbackWitnesses

section AffineTopologyPullbackWitnesses

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Derived pullback along affine topology change exists by the canonical K-flat
construction. -/
instance affineTopologyModulePullbackHasLeftDerivedFunctor :
    (@modulePullbackToDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)).HasLeftDerivedFunctor
        (ModuleQis.{u + 1} (affineChaoticRingedSite X)) := sorry

/-- Derived affine-topology pullback exists pointwise. -/
instance affineTopologyModulePullbackHasPointwiseLeftDerivedFunctor :
    (@modulePullbackToDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance
      (affineTopologyModulePushforwardIsRightAdjoint X)).HasPointwiseLeftDerivedFunctor
        (ModuleQis.{u + 1} (affineChaoticRingedSite X)) := sorry

/-- Derived affine-topology pullback carries its canonical shift comparison. -/
@[implicit_reducible]
noncomputable def affineTopologyModulePullbackCommShift :
    (@modulePullbackDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)
      (affineTopologyModulePullbackHasLeftDerivedFunctor X)).CommShift ℤ :=
  @Functor.totalLeftDerived_commShift _ _ _ inferInstance inferInstance inferInstance
    (@modulePullbackToDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance (affineTopologyModulePushforwardIsRightAdjoint X))
    (ModuleQis.{u + 1} (affineChaoticRingedSite X))
    (moduleLocalization.{u + 1} (affineChaoticRingedSite X))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (affineTopologyModulePullbackHasPointwiseLeftDerivedFunctor X)

end AffineTopologyPullbackWitnesses

/-- Derived pullback along the dense affine étale inclusion preserves quasi-coherent,
sectionwise `u`-small cohomology. -/
theorem extendFromAffineEtale_mapsTo {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affineEtaleProperty X ≤
      (liftedProperty X).inverseImage
        (@modulePullbackDerived.{u + 1} _ _ (affineEtaleRingedSiteHom X)
          inferInstance inferInstance (affineEtaleModulePushforwardIsRightAdjoint X)
          (affineEtaleModulePullbackHasLeftDerivedFunctor X)) := sorry

/-- The dense affine étale comparison supplies the canonical total-derived adjunction. -/
instance affineEtaleHasDerivedAdjunction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    @DerivedAdjunction.HasPair.{u + 1} _ _ (affineEtaleRingedSiteHom X)
      inferInstance inferInstance (affineEtaleModulePushforwardIsRightAdjoint X)
      (affineEtaleModulePushforwardHasRightDerivedFunctor X)
      (affineEtaleModulePullbackHasLeftDerivedFunctor X) := sorry

/-- Derived restriction to the dense affine étale subsite preserves quasi-coherent,
sectionwise `u`-small cohomology. -/
theorem restrictToAffineEtale_mapsTo {S : Scheme.{u}} (X : AlgebraicSpace S) :
    liftedProperty X ≤
      (affineEtaleProperty X).inverseImage
        (@modulePushforwardDerived.{u + 1} _ _ (affineEtaleRingedSiteHom X)
          inferInstance inferInstance
          (affineEtaleModulePushforwardHasRightDerivedFunctor X)) := sorry

/-- Derived pullback from the affine étale model to the lifted small étale model. -/
noncomputable def extendFromAffineEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AffineEtale X ⥤ Lifted X :=
  FullSubcategory.restrict
    (@modulePullbackDerived.{u + 1} _ _ (affineEtaleRingedSiteHom X)
      inferInstance inferInstance (affineEtaleModulePushforwardIsRightAdjoint X)
      (affineEtaleModulePullbackHasLeftDerivedFunctor X))
    (extendFromAffineEtale_mapsTo X)

/-- Canonical derived restriction from the lifted small étale site to its dense affine
étale subsite. -/
noncomputable def restrictToAffineEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Lifted X ⥤ AffineEtale X :=
  FullSubcategory.restrict
    (@modulePushforwardDerived.{u + 1} _ _ (affineEtaleRingedSiteHom X)
      inferInstance inferInstance
      (affineEtaleModulePushforwardHasRightDerivedFunctor X))
    (restrictToAffineEtale_mapsTo X)

/-- The restricted derived adjunction for the dense affine étale inclusion. -/
noncomputable def affineEtaleAdjunction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    extendFromAffineEtale X ⊣ restrictToAffineEtale X :=
  FullSubcategory.adjunction _ _
    (@moduleDerivedAdjunction.{u + 1} _ _ (affineEtaleRingedSiteHom X)
      inferInstance inferInstance (affineEtaleModulePushforwardIsRightAdjoint X)
      (affineEtaleModulePushforwardHasRightDerivedFunctor X)
      (affineEtaleModulePullbackHasLeftDerivedFunctor X)
      (affineEtaleHasDerivedAdjunction X))
    (extendFromAffineEtale_mapsTo X) (restrictToAffineEtale_mapsTo X)

/-- The derived pullback from the affine étale subsite is an equivalence. -/
instance extendFromAffineEtaleIsEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (extendFromAffineEtale X).IsEquivalence := sorry

/-- The derived pullback from the affine étale subsite commutes with shifts. -/
instance extendFromAffineEtaleCommShift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (extendFromAffineEtale X).CommShift ℤ :=
  @Functor.CommShift.ofComp _ _ _ _ _ _ _ _ _
    (FullSubcategory.restrict.compιIso
      (@modulePullbackDerived.{u + 1} _ _ (affineEtaleRingedSiteHom X)
        inferInstance inferInstance (affineEtaleModulePushforwardIsRightAdjoint X)
        (affineEtaleModulePullbackHasLeftDerivedFunctor X))
      (extendFromAffineEtale_mapsTo X)) inferInstance inferInstance ℤ
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Functor.CommShift.comp _ _ _ _ _ _ (affineEtaleProperty X).ι
      (@modulePullbackDerived.{u + 1} _ _ (affineEtaleRingedSiteHom X)
        inferInstance inferInstance (affineEtaleModulePushforwardIsRightAdjoint X)
        (affineEtaleModulePullbackHasLeftDerivedFunctor X)) ℤ
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (affineEtaleModulePullbackCommShift X))

/-- The derived pullback from the affine étale subsite is triangulated. -/
instance extendFromAffineEtaleIsTriangulated {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (extendFromAffineEtale X).IsTriangulated := sorry

/-- The derived pullback from the affine étale subsite is `ℤ`-linear. -/
instance extendFromAffineEtaleLinear {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (extendFromAffineEtale X).Linear ℤ := sorry

/-- Restriction along the affine étale comparison, after universe lifting. -/
noncomputable def toAffineEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    DerivedQCoh X ⥤ AffineEtale X :=
  toLifted X ⋙ restrictToAffineEtale X

/-- Extension from the affine étale presentation, followed by reversing the universe
lift. -/
noncomputable def fromAffineEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AffineEtale X ⥤ DerivedQCoh X :=
  extendFromAffineEtale X ⋙ fromLifted X

/-- The derived category of `𝒪_X`-modules with quasi-coherent cohomology is canonically
linearly and triangulatedly equivalent to its affine étale ringed-site presentation. -/
noncomputable def affineEtaleEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RLinear.TriangulatedEquivalence ℤ (DerivedQCoh X) (AffineEtale X) :=
  RLinear.TriangulatedEquivalence.trans ℤ (liftedEquivalence X)
    (RLinear.TriangulatedEquivalence.symm ℤ
      (RLinear.TriangulatedEquivalence.ofAdjunction ℤ
        (affineEtaleAdjunction X) (extendFromAffineEtaleIsEquivalence X)))

/-- The forward functor first lifts modules on `X`, then restricts to the affine étale
subsite. -/
@[simp]
theorem affineEtaleEquivalence_functor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleEquivalence X).functor = toAffineEtale X := sorry

/-- The inverse functor extends from the affine étale subsite, then reverses the
universe lift. -/
@[simp]
theorem affineEtaleEquivalence_inverse {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleEquivalence X).inverse = fromAffineEtale X := sorry

/-- The affine topology-change comparison supplies the canonical total-derived
adjunction. -/
instance affineTopologyHasDerivedAdjunction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    @DerivedAdjunction.HasPair.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)
      (affineTopologyModulePushforwardHasRightDerivedFunctor X)
      (affineTopologyModulePullbackHasLeftDerivedFunctor X) := sorry

/-- Derived affine topology pullback preserves quasi-coherent, sectionwise `u`-small
cohomology. -/
theorem affinePullback_mapsTo {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affineProperty X ≤
      (affineEtaleProperty X).inverseImage
        (@modulePullbackDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
          inferInstance inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)
          (affineTopologyModulePullbackHasLeftDerivedFunctor X)) := sorry

/-- Derived affine topology pushforward preserves quasi-coherent, sectionwise `u`-small
cohomology. -/
theorem affinePushforward_mapsTo {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affineEtaleProperty X ≤
      (affineProperty X).inverseImage
        (@modulePushforwardDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
          inferInstance inferInstance
          (affineTopologyModulePushforwardHasRightDerivedFunctor X)) := sorry

/-- The restricted derived inverse image `ε^*` from the chaotic to the étale affine
site. -/
noncomputable def affinePullback {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Affine X ⥤ AffineEtale X :=
  FullSubcategory.restrict
    (@modulePullbackDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)
      (affineTopologyModulePullbackHasLeftDerivedFunctor X))
    (affinePullback_mapsTo X)

/-- The restricted derived direct image `Rε_*` from the étale to the chaotic affine
site. -/
noncomputable def affinePushforward {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AffineEtale X ⥤ Affine X :=
  FullSubcategory.restrict
    (@modulePushforwardDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance inferInstance
      (affineTopologyModulePushforwardHasRightDerivedFunctor X))
    (affinePushforward_mapsTo X)

/-- The restricted affine topology-change adjunction `ε^* ⊣ Rε_*`. -/
noncomputable def affineAdjunction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affinePullback X ⊣ affinePushforward X :=
  FullSubcategory.adjunction _ _
    (@moduleDerivedAdjunction.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)
      (affineTopologyModulePushforwardHasRightDerivedFunctor X)
      (affineTopologyModulePullbackHasLeftDerivedFunctor X)
      (affineTopologyHasDerivedAdjunction X))
    (affinePullback_mapsTo X) (affinePushforward_mapsTo X)

/-- Affine topology pullback is an equivalence. -/
instance affinePullbackIsEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affinePullback X).IsEquivalence := sorry

/-- Affine topology pullback commutes with shifts. -/
instance affinePullbackCommShift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affinePullback X).CommShift ℤ :=
  @Functor.CommShift.ofComp _ _ _ _ _ _ _ _ _
    (FullSubcategory.restrict.compιIso
      (@modulePullbackDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
        inferInstance inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)
        (affineTopologyModulePullbackHasLeftDerivedFunctor X))
      (affinePullback_mapsTo X)) inferInstance inferInstance ℤ
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Functor.CommShift.comp _ _ _ _ _ _ (affineProperty X).ι
      (@modulePullbackDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
        inferInstance inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)
        (affineTopologyModulePullbackHasLeftDerivedFunctor X)) ℤ
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (affineTopologyModulePullbackCommShift X))

/-- Affine topology pullback is triangulated. -/
instance affinePullbackIsTriangulated {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affinePullback X).IsTriangulated := sorry

/-- Affine topology pullback is `ℤ`-linear. -/
instance affinePullbackLinear {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affinePullback X).Linear ℤ := sorry

/-- The quasi-coherent derived categories on the affine étale and affine chaotic
sites are canonically linearly and triangulatedly equivalent. -/
noncomputable def affineTopologyEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RLinear.TriangulatedEquivalence ℤ (AffineEtale X) (Affine X) :=
  RLinear.TriangulatedEquivalence.symm ℤ
    (RLinear.TriangulatedEquivalence.ofAdjunction ℤ
      (affineAdjunction X) (affinePullbackIsEquivalence X))

/-- The forward functor of the affine-topology equivalence is derived pushforward. -/
@[simp]
theorem affineTopologyEquivalence_functor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineTopologyEquivalence X).functor = affinePushforward X := sorry

/-- The inverse functor of the affine-topology equivalence is derived pullback. -/
@[simp]
theorem affineTopologyEquivalence_inverse {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineTopologyEquivalence X).inverse = affinePullback X := sorry

/-- The identity ambient functor maps cohomological affine objects to comparison-defined
ones, with the same sectionwise `u`-small cohomology condition. -/
theorem toAffineQC_mapsTo {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affineProperty X ≤ (affineQCProperty X).inverseImage (𝟭 _) := sorry

/-- The identity ambient functor maps comparison-defined affine objects to cohomological
ones, with the same sectionwise `u`-small cohomology condition. -/
theorem fromAffineQC_mapsTo {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affineQCProperty X ≤ (affineProperty X).inverseImage (𝟭 _) := sorry

/-- The canonical identity-on-ambient comparison from affine cohomological objects to
`QC`. -/
noncomputable def toAffineQC {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Affine X ⥤ AffineQC X :=
  FullSubcategory.restrict (𝟭 _) (toAffineQC_mapsTo X)

/-- The canonical identity-on-ambient comparison from `QC` to affine cohomological
objects. -/
noncomputable def fromAffineQC {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AffineQC X ⥤ Affine X :=
  FullSubcategory.restrict (𝟭 _) (fromAffineQC_mapsTo X)

/-- The identity ambient adjunction restricted across the two affine quasi-coherence
properties. -/
noncomputable def affineQCAdjunction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    toAffineQC X ⊣ fromAffineQC X :=
  FullSubcategory.adjunction _ _ (Adjunction.id)
    (toAffineQC_mapsTo X) (fromAffineQC_mapsTo X)

/-- The comparison from affine cohomological objects to `QC` is an equivalence. -/
instance toAffineQCIsEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (toAffineQC X).IsEquivalence := sorry

/-- The comparison from affine cohomological objects to `QC` commutes with shifts. -/
instance toAffineQCCommShift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (toAffineQC X).CommShift ℤ :=
  Functor.CommShift.ofComp
    (FullSubcategory.restrict.compιIso (𝟭 _) (toAffineQC_mapsTo X)) ℤ

/-- The comparison from affine cohomological objects to `QC` is triangulated. -/
instance toAffineQCIsTriangulated {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (toAffineQC X).IsTriangulated := sorry

/-- The comparison from affine cohomological objects to `QC` is `ℤ`-linear. -/
instance toAffineQCLinear {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (toAffineQC X).Linear ℤ := sorry

/-- Quasi-coherent cohomology on the affine chaotic site is canonically linearly and
triangulatedly equivalent to the comparison-map category `QC(X_affine, 𝒪)`. -/
noncomputable def affineQCEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RLinear.TriangulatedEquivalence ℤ (Affine X) (AffineQC X) :=
  RLinear.TriangulatedEquivalence.ofAdjunction ℤ
    (affineQCAdjunction X) (toAffineQCIsEquivalence X)

/-- The forward functor of the affine-`QC` equivalence is the canonical comparison. -/
@[simp]
theorem affineQCEquivalence_functor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineQCEquivalence X).functor = toAffineQC X := sorry

/-- The inverse functor of the affine-`QC` equivalence is the canonical reverse
comparison. -/
@[simp]
theorem affineQCEquivalence_inverse {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineQCEquivalence X).inverse = fromAffineQC X := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
