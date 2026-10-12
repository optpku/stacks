/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.KFlat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.SiteModels

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- An ordinary structure-sheaf module on an open, lifted to the module universe of the
lifted-opens presentation. -/
noncomputable abbrev opensModuleLiftObj (X : Scheme.{u})
    (M : X.toRingedSpace.Modules) (U : X.Opensᵒᵖ) :
    ModuleCat.{u + 1} ((liftedOpensRingSheaf X).obj.obj U) :=
  (ModuleCat.restrictScalars
    (ULift.ringEquiv.{u, u + 1}.toRingHom.comp
      (CommRingCat.liftedMap ((X.restrictFunctorΓ).hom.app U)).hom)).obj
      ((ModuleCat.uliftFunctor.{u + 1, u} (X.ringCatSheaf.obj.obj U)).obj
        (M.val.obj U))

/-- Universe lifting of a morphism between modules on an open of `X`. -/
noncomputable def opensModuleLiftMap (X : Scheme.{u})
    {M N : X.toRingedSpace.Modules} (f : M ⟶ N) (U : X.Opensᵒᵖ) :
    opensModuleLiftObj X M U ⟶ opensModuleLiftObj X N U :=
  let source : ModuleCat.{u + 1} ((liftedOpensRingSheaf X).obj.obj U) :=
    opensModuleLiftObj X M U
  let target : ModuleCat.{u + 1} ((liftedOpensRingSheaf X).obj.obj U) :=
    opensModuleLiftObj X N U
  @ModuleCat.ofHom _ _ (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun x ↦ ULift.up (f.val.app U x.down)
      map_add' := sorry
      map_smul' := sorry }

/-- The scalar-restricted target of a lifted restriction map on opens. -/
noncomputable abbrev opensModuleLiftRestrictionTarget (X : Scheme.{u})
    (M : X.toRingedSpace.Modules) {U V : X.Opensᵒᵖ} (f : U ⟶ V) :=
  (ModuleCat.restrictScalars (((liftedOpensRingSheaf X).obj.map f).hom)).obj
    (opensModuleLiftObj X M V)

/-- Universe lifting of a module restriction map on the opens of `X`. -/
noncomputable def opensModuleLiftRestrictionMap (X : Scheme.{u})
    (M : X.toRingedSpace.Modules) {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    opensModuleLiftObj X M U ⟶ opensModuleLiftRestrictionTarget X M f :=
  let source : ModuleCat.{u + 1} ((liftedOpensRingSheaf X).obj.obj U) :=
    opensModuleLiftObj X M U
  let target : ModuleCat.{u + 1} ((liftedOpensRingSheaf X).obj.obj U) :=
    opensModuleLiftRestrictionTarget X M f
  @ModuleCat.ofHom _ _ (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun x ↦ ULift.up (M.val.map f x.down)
      map_add' := sorry
      map_smul' := sorry }

/-- The objectwise universe lift of a module presheaf on the opens of `X`. -/
noncomputable def opensModuleLiftPresheaf (X : Scheme.{u})
    (M : X.toRingedSpace.Modules) :
    _root_.PresheafOfModules.{u + 1} (liftedOpensRingSheaf X).obj where
  obj := opensModuleLiftObj X M
  map := opensModuleLiftRestrictionMap X M
  map_id := sorry
  map_comp := sorry

/-- Objectwise universe lifting preserves the sheaf condition on the opens of `X`. -/
theorem opensModuleLiftPresheaf_isSheaf (X : Scheme.{u})
    (M : X.toRingedSpace.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (X : TopCat))
      (opensModuleLiftPresheaf X M).presheaf := sorry

/-- Universe lifting of a module sheaf on the opens of `X`. -/
noncomputable def opensModuleLiftSheafObj (X : Scheme.{u})
    (M : X.toRingedSpace.Modules) :
    RingedSite.ModuleCat.{u + 1} (liftedOpensRingedSite X) :=
  ⟨opensModuleLiftPresheaf X M, opensModuleLiftPresheaf_isSheaf X M⟩

/-- Universe lifting of a morphism of module sheaves on the opens of `X`. -/
noncomputable def opensModuleLiftSheafMap (X : Scheme.{u})
    {M N : X.toRingedSpace.Modules} (f : M ⟶ N) :
    opensModuleLiftSheafObj X M ⟶ opensModuleLiftSheafObj X N :=
  ⟨fun U ↦ opensModuleLiftMap X f U, sorry⟩

/-- The exact objectwise universe-lift functor from ordinary modules on `X` to the
lifted-opens presentation. -/
noncomputable def opensModuleLift (X : Scheme.{u}) :
    X.toRingedSpace.Modules ⥤ₑ RingedSite.ModuleCat.{u + 1} (liftedOpensRingedSite X) :=
  ⟨{ obj := opensModuleLiftSheafObj X
     map := opensModuleLiftSheafMap X
     map_id := sorry
     map_comp := sorry },
   sorry⟩

/-- The derived objectwise universe lift from ordinary modules on `X` to the lifted-opens
presentation. -/
noncomputable abbrev opensModuleLiftDerived (X : Scheme.{u}) :
    DerivedCategory X.toRingedSpace.Modules ⥤
      RingedSite.Hom.ModuleDerived.{u + 1} (liftedOpensRingedSite X) :=
  @Functor.mapDerivedCategory
    X.toRingedSpace.Modules inferInstance inferInstance inferInstance
    (RingedSite.ModuleCat.{u + 1} (liftedOpensRingedSite X)) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (liftedOpensRingedSite X))
    (opensModuleLift X).obj inferInstance inferInstance inferInstance

/-- Derived universe lifting preserves quasi-coherent cohomology. -/
theorem toOpens_mapsTo (X : Scheme.{u}) :
    DerivedCategory.cohomologyIn (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (opensProperty X).inverseImage (opensModuleLiftDerived X) := sorry

/-- The canonical universe-lift comparison from `D_QCoh(𝒪_X)` to its lifted-opens
presentation. -/
noncomputable def toOpens (X : Scheme.{u}) : DerivedCategory.CohomologyIn (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⥤ Opens X :=
  FullSubcategory.restrict (opensModuleLiftDerived X) (toOpens_mapsTo X)

/-- The universe-lift comparison from `D_QCoh(𝒪_X)` is an equivalence. -/
instance toOpensIsEquivalence (X : Scheme.{u}) : (toOpens X).IsEquivalence := sorry

/-- The reverse universe transport from the lifted-opens presentation to `D_QCoh(𝒪_X)`. -/
noncomputable def fromOpens (X : Scheme.{u}) : Opens X ⥤ DerivedCategory.CohomologyIn (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) where
  obj K := (toOpens X).objPreimage K
  map {K L} f :=
    (toOpens X).preimage (
      ((toOpens X).objObjPreimageIso K).hom ≫ f ≫
        ((toOpens X).objObjPreimageIso L).inv)
  map_id := sorry
  map_comp := sorry

/-- Universe lifting is left adjoint to the explicit reverse universe transport. -/
noncomputable def opensAdjunction (X : Scheme.{u}) : toOpens X ⊣ fromOpens X where
  unit :=
    { app := fun K ↦
        ((toOpens X).preimageIso
          ((toOpens X).objObjPreimageIso ((toOpens X).obj K))).inv
      naturality := sorry }
  counit :=
    { app := fun K ↦ ((toOpens X).objObjPreimageIso K).hom
      naturality := sorry }
  left_triangle_components := sorry
  right_triangle_components := sorry

/-- The universe-lift comparison from `D_QCoh(𝒪_X)` commutes with shifts. -/
instance toOpensCommShift (X : Scheme.{u}) : (toOpens X).CommShift ℤ :=
  Functor.CommShift.ofComp
    (FullSubcategory.restrict.compιIso (opensModuleLiftDerived X) (toOpens_mapsTo X)) ℤ

/-- The universe-lift comparison from `D_QCoh(𝒪_X)` is triangulated. -/
instance toOpensIsTriangulated (X : Scheme.{u}) : (toOpens X).IsTriangulated := sorry

/-- The universe-lift comparison from `D_QCoh(𝒪_X)` is `ℤ`-linear. -/
instance toOpensLinear (X : Scheme.{u}) : (toOpens X).Linear ℤ := sorry

/-- The canonical linear triangulated equivalence between `D_QCoh(𝒪_X)` and its
lifted-opens presentation. -/
noncomputable def opensEquivalence (X : Scheme.{u}) :
    RLinear.TriangulatedEquivalence ℤ (DerivedCategory.CohomologyIn (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (Opens X) :=
  RLinear.TriangulatedEquivalence.ofAdjunction ℤ
    (opensAdjunction X) (toOpensIsEquivalence X)

/-- The inverse of the opens equivalence is the explicit reverse universe transport. -/
@[simp]
theorem opensEquivalence_inverse (X : Scheme.{u}) :
    (opensEquivalence X).inverse = fromOpens X := sorry

/-- Small-Zariski module pushforward has its canonical inverse-image left adjoint. -/
theorem smallZariskiModulePushforwardIsRightAdjoint (X : Scheme.{u}) :
    ((liftedSmallZariskiRingedSiteHom X).modulePushforward.{u + 1}).IsRightAdjoint := sorry

/-- Module pushforward from the affine Zariski site has its canonical inverse-image left adjoint. -/
theorem affineZariskiModulePushforwardIsRightAdjoint (X : Scheme.{u}) :
    ((affineZariskiRingedSiteHom X).modulePushforward.{u + 1}).IsRightAdjoint := sorry

/-- Affine-topology module pushforward has its canonical inverse-image left adjoint. -/
theorem affineTopologyModulePushforwardIsRightAdjoint (X : Scheme.{u}) :
    ((affineTopologyRingedSiteHom X).modulePushforward.{u + 1}).IsRightAdjoint := sorry

/-- Small-Zariski module pushforward admits its canonical total right-derived functor. -/
theorem smallZariskiModulePushforwardHasRightDerivedFunctor (X : Scheme.{u}) :
    (modulePushforwardToDerived.{u + 1}
      (liftedSmallZariskiRingedSiteHom X)).HasRightDerivedFunctor
        (ModuleQis.{u + 1} (smallZariskiRingedSite X)) := sorry

/-- Module pushforward from the affine Zariski site admits its canonical total right-derived
functor. -/
theorem affineZariskiModulePushforwardHasRightDerivedFunctor (X : Scheme.{u}) :
    (modulePushforwardToDerived.{u + 1}
      (affineZariskiRingedSiteHom X)).HasRightDerivedFunctor
        (ModuleQis.{u + 1} (smallZariskiRingedSite X)) := sorry

/-- Affine-topology module pushforward admits its canonical total right-derived functor. -/
theorem affineTopologyModulePushforwardHasRightDerivedFunctor (X : Scheme.{u}) :
    (modulePushforwardToDerived.{u + 1}
      (affineTopologyRingedSiteHom X)).HasRightDerivedFunctor
        (ModuleQis.{u + 1} (affineZariskiRingedSite X)) := sorry

section SmallZariskiPullbackWitnesses

variable (X : Scheme.{u})

/-- Derived pullback along the small-Zariski comparison exists by the canonical
K-flat construction. -/
theorem smallZariskiModulePullbackHasLeftDerivedFunctor :
    (@modulePullbackToDerived.{u + 1} _ _ (liftedSmallZariskiRingedSiteHom X)
      inferInstance (smallZariskiModulePushforwardIsRightAdjoint X)).HasLeftDerivedFunctor
        (ModuleQis.{u + 1} (liftedOpensRingedSite X)) := sorry

/-- Derived pullback to the small Zariski site exists pointwise. -/
theorem smallZariskiModulePullbackHasPointwiseLeftDerivedFunctor :
    (@modulePullbackToDerived.{u + 1} _ _ (liftedSmallZariskiRingedSiteHom X)
      inferInstance (smallZariskiModulePushforwardIsRightAdjoint X)).HasPointwiseLeftDerivedFunctor
        (ModuleQis.{u + 1} (liftedOpensRingedSite X)) := sorry

/-- Derived pullback to the small Zariski site carries its canonical shift comparison. -/
@[implicit_reducible]
noncomputable def smallZariskiModulePullbackCommShift :
    (@modulePullbackDerived.{u + 1} _ _ (liftedSmallZariskiRingedSiteHom X)
      inferInstance inferInstance (smallZariskiModulePushforwardIsRightAdjoint X)
      (smallZariskiModulePullbackHasLeftDerivedFunctor X)).CommShift ℤ :=
  @Functor.totalLeftDerived_commShift _ _ _ inferInstance inferInstance inferInstance
    (@modulePullbackToDerived.{u + 1} _ _ (liftedSmallZariskiRingedSiteHom X)
      inferInstance (smallZariskiModulePushforwardIsRightAdjoint X))
    (ModuleQis.{u + 1} (liftedOpensRingedSite X))
    (moduleLocalization.{u + 1} (liftedOpensRingedSite X))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (smallZariskiModulePullbackHasPointwiseLeftDerivedFunctor X)

end SmallZariskiPullbackWitnesses

section AffineZariskiPullbackWitnesses

variable (X : Scheme.{u})

/-- Derived pullback along the affine-Zariski comparison exists by the canonical
K-flat construction. -/
theorem affineZariskiModulePullbackHasLeftDerivedFunctor :
    (@modulePullbackToDerived.{u + 1} _ _ (affineZariskiRingedSiteHom X)
      inferInstance (affineZariskiModulePushforwardIsRightAdjoint X)).HasLeftDerivedFunctor
        (ModuleQis.{u + 1} (affineZariskiRingedSite X)) := sorry

/-- Derived pullback from the affine Zariski site exists pointwise. -/
theorem affineZariskiModulePullbackHasPointwiseLeftDerivedFunctor :
    (@modulePullbackToDerived.{u + 1} _ _ (affineZariskiRingedSiteHom X)
      inferInstance
      (affineZariskiModulePushforwardIsRightAdjoint X)).HasPointwiseLeftDerivedFunctor
        (ModuleQis.{u + 1} (affineZariskiRingedSite X)) := sorry

/-- Derived pullback from the affine Zariski site carries its canonical shift comparison. -/
@[implicit_reducible]
noncomputable def affineZariskiModulePullbackCommShift :
    (@modulePullbackDerived.{u + 1} _ _ (affineZariskiRingedSiteHom X)
      inferInstance inferInstance (affineZariskiModulePushforwardIsRightAdjoint X)
      (affineZariskiModulePullbackHasLeftDerivedFunctor X)).CommShift ℤ :=
  @Functor.totalLeftDerived_commShift _ _ _ inferInstance inferInstance inferInstance
    (@modulePullbackToDerived.{u + 1} _ _ (affineZariskiRingedSiteHom X)
      inferInstance (affineZariskiModulePushforwardIsRightAdjoint X))
    (ModuleQis.{u + 1} (affineZariskiRingedSite X))
    (moduleLocalization.{u + 1} (affineZariskiRingedSite X))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (affineZariskiModulePullbackHasPointwiseLeftDerivedFunctor X)

end AffineZariskiPullbackWitnesses

section AffineTopologyPullbackWitnesses

variable (X : Scheme.{u})

/-- Derived pullback along affine topology change exists by the canonical K-flat construction. -/
theorem affineTopologyModulePullbackHasLeftDerivedFunctor :
    (@modulePullbackToDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)).HasLeftDerivedFunctor
        (ModuleQis.{u + 1} (affineChaoticRingedSite X)) := sorry

/-- Derived affine-topology pullback exists pointwise. -/
theorem affineTopologyModulePullbackHasPointwiseLeftDerivedFunctor :
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

/-- The small-Zariski ringed equivalence supplies the canonical total-derived adjunction. -/
theorem smallZariskiHasDerivedAdjunction (X : Scheme.{u}) :
    @DerivedAdjunction.HasPair.{u + 1} _ _ (liftedSmallZariskiRingedSiteHom X)
      inferInstance inferInstance (smallZariskiModulePushforwardIsRightAdjoint X)
      (smallZariskiModulePushforwardHasRightDerivedFunctor X)
      (smallZariskiModulePullbackHasLeftDerivedFunctor X) := sorry

/-- Derived pullback along the small-Zariski ringed-site comparison preserves
quasi-coherent cohomology. -/
theorem toSmallZariski_mapsTo (X : Scheme.{u}) :
    opensProperty X ≤
      (smallZariskiProperty X).inverseImage
        (@modulePullbackDerived.{u + 1} _ _ (liftedSmallZariskiRingedSiteHom X)
          inferInstance inferInstance (smallZariskiModulePushforwardIsRightAdjoint X)
          (smallZariskiModulePullbackHasLeftDerivedFunctor X)) := sorry

/-- Derived pushforward along the small-Zariski ringed-site comparison preserves
quasi-coherent cohomology. -/
theorem fromSmallZariski_mapsTo (X : Scheme.{u}) :
    smallZariskiProperty X ≤
      (opensProperty X).inverseImage
        (@modulePushforwardDerived.{u + 1} _ _ (liftedSmallZariskiRingedSiteHom X)
          inferInstance inferInstance
          (smallZariskiModulePushforwardHasRightDerivedFunctor X)) := sorry

/-- The canonical derived pullback from `D_QCoh(𝒪_X)` to the small-Zariski model. -/
noncomputable def toSmallZariski (X : Scheme.{u}) :
    Opens X ⥤ SmallZariski X :=
  FullSubcategory.restrict
    (@modulePullbackDerived.{u + 1} _ _ (liftedSmallZariskiRingedSiteHom X)
      inferInstance inferInstance (smallZariskiModulePushforwardIsRightAdjoint X)
      (smallZariskiModulePullbackHasLeftDerivedFunctor X))
    (toSmallZariski_mapsTo X)

/-- The canonical derived pushforward from the small-Zariski model to `D_QCoh(𝒪_X)`. -/
noncomputable def fromSmallZariski (X : Scheme.{u}) :
    SmallZariski X ⥤ Opens X :=
  FullSubcategory.restrict
    (@modulePushforwardDerived.{u + 1} _ _ (liftedSmallZariskiRingedSiteHom X)
      inferInstance inferInstance
      (smallZariskiModulePushforwardHasRightDerivedFunctor X))
    (fromSmallZariski_mapsTo X)

/-- The canonical restricted derived pullback--pushforward adjunction for the small Zariski site. -/
noncomputable def smallZariskiAdjunction (X : Scheme.{u}) :
    toSmallZariski X ⊣ fromSmallZariski X :=
  FullSubcategory.adjunction _ _
    (@moduleDerivedAdjunction.{u + 1} _ _ (liftedSmallZariskiRingedSiteHom X)
      inferInstance inferInstance (smallZariskiModulePushforwardIsRightAdjoint X)
      (smallZariskiModulePushforwardHasRightDerivedFunctor X)
      (smallZariskiModulePullbackHasLeftDerivedFunctor X)
      (smallZariskiHasDerivedAdjunction X))
    (toSmallZariski_mapsTo X) (fromSmallZariski_mapsTo X)

/-- The canonical small-Zariski comparison is an equivalence. -/
instance toSmallZariskiIsEquivalence (X : Scheme.{u}) :
    (toSmallZariski X).IsEquivalence := sorry

/-- The canonical small-Zariski comparison commutes with shifts. -/
instance toSmallZariskiCommShift (X : Scheme.{u}) :
    (toSmallZariski X).CommShift ℤ :=
  @Functor.CommShift.ofComp _ _ _ _ _ _ _ _ _
    (FullSubcategory.restrict.compιIso
      (@modulePullbackDerived.{u + 1} _ _ (liftedSmallZariskiRingedSiteHom X)
        inferInstance inferInstance (smallZariskiModulePushforwardIsRightAdjoint X)
        (smallZariskiModulePullbackHasLeftDerivedFunctor X))
      (toSmallZariski_mapsTo X)) inferInstance inferInstance ℤ
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Functor.CommShift.comp _ _ _ _ _ _ (opensProperty X).ι
      (@modulePullbackDerived.{u + 1} _ _ (liftedSmallZariskiRingedSiteHom X)
        inferInstance inferInstance (smallZariskiModulePushforwardIsRightAdjoint X)
        (smallZariskiModulePullbackHasLeftDerivedFunctor X)) ℤ
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (smallZariskiModulePullbackCommShift X))

/-- The canonical small-Zariski comparison is triangulated. -/
instance toSmallZariskiIsTriangulated (X : Scheme.{u}) :
    (toSmallZariski X).IsTriangulated := sorry

/-- The canonical small-Zariski comparison is `ℤ`-linear. -/
instance toSmallZariskiLinear (X : Scheme.{u}) :
    (toSmallZariski X).Linear ℤ := sorry

/-- Derived pullback along the dense affine inclusion preserves quasi-coherent cohomology. -/
theorem extendFromAffine_mapsTo (X : Scheme.{u}) :
    affineZariskiProperty X ≤
      (smallZariskiProperty X).inverseImage
        (@modulePullbackDerived.{u + 1} _ _ (affineZariskiRingedSiteHom X)
          inferInstance inferInstance (affineZariskiModulePushforwardIsRightAdjoint X)
          (affineZariskiModulePullbackHasLeftDerivedFunctor X)) := sorry

/-- The dense affine comparison supplies the canonical total-derived adjunction. -/
theorem affineZariskiHasDerivedAdjunction (X : Scheme.{u}) :
    @DerivedAdjunction.HasPair.{u + 1} _ _ (affineZariskiRingedSiteHom X)
      inferInstance inferInstance (affineZariskiModulePushforwardIsRightAdjoint X)
      (affineZariskiModulePushforwardHasRightDerivedFunctor X)
      (affineZariskiModulePullbackHasLeftDerivedFunctor X) := sorry

/-- Derived restriction to the dense affine subsite preserves quasi-coherent cohomology. -/
theorem restrictToAffine_mapsTo (X : Scheme.{u}) :
    smallZariskiProperty X ≤
      (affineZariskiProperty X).inverseImage
        (@modulePushforwardDerived.{u + 1} _ _ (affineZariskiRingedSiteHom X)
          inferInstance inferInstance
          (affineZariskiModulePushforwardHasRightDerivedFunctor X)) := sorry

/-- Derived pullback from the affine Zariski model to the small-Zariski model. -/
noncomputable def extendFromAffine (X : Scheme.{u}) :
    AffineZariski X ⥤ SmallZariski X :=
  FullSubcategory.restrict
    (@modulePullbackDerived.{u + 1} _ _ (affineZariskiRingedSiteHom X)
      inferInstance inferInstance (affineZariskiModulePushforwardIsRightAdjoint X)
      (affineZariskiModulePullbackHasLeftDerivedFunctor X))
    (extendFromAffine_mapsTo X)

/-- Canonical derived restriction from the small Zariski site to its dense affine subsite. -/
noncomputable def restrictToAffine (X : Scheme.{u}) :
    SmallZariski X ⥤ AffineZariski X :=
  FullSubcategory.restrict
    (@modulePushforwardDerived.{u + 1} _ _ (affineZariskiRingedSiteHom X)
      inferInstance inferInstance
      (affineZariskiModulePushforwardHasRightDerivedFunctor X))
    (restrictToAffine_mapsTo X)

/-- The restricted derived adjunction for the dense affine inclusion. -/
noncomputable def affineZariskiAdjunction (X : Scheme.{u}) :
    extendFromAffine X ⊣ restrictToAffine X :=
  FullSubcategory.adjunction _ _
    (@moduleDerivedAdjunction.{u + 1} _ _ (affineZariskiRingedSiteHom X)
      inferInstance inferInstance (affineZariskiModulePushforwardIsRightAdjoint X)
      (affineZariskiModulePushforwardHasRightDerivedFunctor X)
      (affineZariskiModulePullbackHasLeftDerivedFunctor X)
      (affineZariskiHasDerivedAdjunction X))
    (extendFromAffine_mapsTo X) (restrictToAffine_mapsTo X)

/-- The derived pullback from the affine subsite is an equivalence. -/
instance extendFromAffineIsEquivalence (X : Scheme.{u}) :
    (extendFromAffine X).IsEquivalence := sorry

/-- The derived pullback from the affine subsite commutes with shifts. -/
instance extendFromAffineCommShift (X : Scheme.{u}) :
    (extendFromAffine X).CommShift ℤ :=
  @Functor.CommShift.ofComp _ _ _ _ _ _ _ _ _
    (FullSubcategory.restrict.compιIso
      (@modulePullbackDerived.{u + 1} _ _ (affineZariskiRingedSiteHom X)
        inferInstance inferInstance (affineZariskiModulePushforwardIsRightAdjoint X)
        (affineZariskiModulePullbackHasLeftDerivedFunctor X))
      (extendFromAffine_mapsTo X)) inferInstance inferInstance ℤ
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Functor.CommShift.comp _ _ _ _ _ _ (affineZariskiProperty X).ι
      (@modulePullbackDerived.{u + 1} _ _ (affineZariskiRingedSiteHom X)
        inferInstance inferInstance (affineZariskiModulePushforwardIsRightAdjoint X)
        (affineZariskiModulePullbackHasLeftDerivedFunctor X)) ℤ
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (affineZariskiModulePullbackCommShift X))

/-- The derived pullback from the affine subsite is triangulated. -/
instance extendFromAffineIsTriangulated (X : Scheme.{u}) :
    (extendFromAffine X).IsTriangulated := sorry

/-- The derived pullback from the affine subsite is `ℤ`-linear. -/
instance extendFromAffineLinear (X : Scheme.{u}) :
    (extendFromAffine X).Linear ℤ := sorry

/-- The affine topology-change morphism supplies the canonical total-derived adjunction. -/
theorem affineTopologyHasDerivedAdjunction (X : Scheme.{u}) :
    @DerivedAdjunction.HasPair.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)
      (affineTopologyModulePushforwardHasRightDerivedFunctor X)
      (affineTopologyModulePullbackHasLeftDerivedFunctor X) := sorry

/-- Derived affine topology pullback preserves quasi-coherent cohomology. -/
theorem affinePullback_mapsTo (X : Scheme.{u}) :
    affineProperty X ≤
      (affineZariskiProperty X).inverseImage
        (@modulePullbackDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
          inferInstance inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)
          (affineTopologyModulePullbackHasLeftDerivedFunctor X)) := sorry

/-- Derived affine topology pushforward preserves quasi-coherent cohomology. -/
theorem affinePushforward_mapsTo (X : Scheme.{u}) :
    affineZariskiProperty X ≤
      (affineProperty X).inverseImage
        (@modulePushforwardDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
          inferInstance inferInstance
          (affineTopologyModulePushforwardHasRightDerivedFunctor X)) := sorry

/-- The restricted derived inverse image `Lε^*` from the chaotic to the Zariski affine site. -/
noncomputable def affinePullback (X : Scheme.{u}) : Affine X ⥤ AffineZariski X :=
  FullSubcategory.restrict
    (@modulePullbackDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)
      (affineTopologyModulePullbackHasLeftDerivedFunctor X))
    (affinePullback_mapsTo X)

/-- The restricted derived direct image `Rε_*` from the Zariski to the chaotic affine site. -/
noncomputable def affinePushforward (X : Scheme.{u}) : AffineZariski X ⥤ Affine X :=
  FullSubcategory.restrict
    (@modulePushforwardDerived.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance inferInstance
      (affineTopologyModulePushforwardHasRightDerivedFunctor X))
    (affinePushforward_mapsTo X)

/-- The restricted affine topology-change adjunction `Lε^* ⊣ Rε_*`. -/
noncomputable def affineAdjunction (X : Scheme.{u}) :
    affinePullback X ⊣ affinePushforward X :=
  FullSubcategory.adjunction _ _
    (@moduleDerivedAdjunction.{u + 1} _ _ (affineTopologyRingedSiteHom X)
      inferInstance inferInstance (affineTopologyModulePushforwardIsRightAdjoint X)
      (affineTopologyModulePushforwardHasRightDerivedFunctor X)
      (affineTopologyModulePullbackHasLeftDerivedFunctor X)
      (affineTopologyHasDerivedAdjunction X))
    (affinePullback_mapsTo X) (affinePushforward_mapsTo X)

/-- Affine topology pullback is an equivalence. -/
instance affinePullbackIsEquivalence (X : Scheme.{u}) :
    (affinePullback X).IsEquivalence := sorry

/-- Affine topology pullback commutes with shifts. -/
instance affinePullbackCommShift (X : Scheme.{u}) :
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
instance affinePullbackIsTriangulated (X : Scheme.{u}) :
    (affinePullback X).IsTriangulated := sorry

/-- Affine topology pullback is `ℤ`-linear. -/
instance affinePullbackLinear (X : Scheme.{u}) :
    (affinePullback X).Linear ℤ := sorry

/-- The identity ambient functor maps cohomological affine objects to comparison-defined ones. -/
theorem toAffineQC_mapsTo (X : Scheme.{u}) :
    affineProperty X ≤ (affineQCProperty X).inverseImage (𝟭 _) := sorry

/-- The identity ambient functor maps comparison-defined affine objects to cohomological ones. -/
theorem fromAffineQC_mapsTo (X : Scheme.{u}) :
    affineQCProperty X ≤ (affineProperty X).inverseImage (𝟭 _) := sorry

/-- The canonical identity-on-ambient comparison from affine cohomological objects to `QC`. -/
noncomputable def toAffineQC (X : Scheme.{u}) : Affine X ⥤ AffineQC X :=
  FullSubcategory.restrict (𝟭 _) (toAffineQC_mapsTo X)

/-- The canonical identity-on-ambient comparison from `QC` to affine cohomological objects. -/
noncomputable def fromAffineQC (X : Scheme.{u}) : AffineQC X ⥤ Affine X :=
  FullSubcategory.restrict (𝟭 _) (fromAffineQC_mapsTo X)

/-- The identity ambient adjunction restricted across the two affine quasi-coherence properties. -/
noncomputable def affineQCAdjunction (X : Scheme.{u}) :
    toAffineQC X ⊣ fromAffineQC X :=
  FullSubcategory.adjunction _ _ (Adjunction.id)
    (toAffineQC_mapsTo X) (fromAffineQC_mapsTo X)

/-- The comparison from affine cohomological objects to `QC` is an equivalence. -/
instance toAffineQCIsEquivalence (X : Scheme.{u}) :
    (toAffineQC X).IsEquivalence := sorry

/-- The comparison from affine cohomological objects to `QC` commutes with shifts. -/
instance toAffineQCCommShift (X : Scheme.{u}) :
    (toAffineQC X).CommShift ℤ :=
  Functor.CommShift.ofComp
    (FullSubcategory.restrict.compιIso (𝟭 _) (toAffineQC_mapsTo X)) ℤ

/-- The comparison from affine cohomological objects to `QC` is triangulated. -/
instance toAffineQCIsTriangulated (X : Scheme.{u}) :
    (toAffineQC X).IsTriangulated := sorry

/-- The comparison from affine cohomological objects to `QC` is `ℤ`-linear. -/
instance toAffineQCLinear (X : Scheme.{u}) :
    (toAffineQC X).Linear ℤ := sorry


/-- The derived category of `𝒪_X`-modules with quasi-coherent cohomology is canonically
linearly and triangulatedly equivalent to its small Zariski ringed-site presentation. -/
noncomputable def smallZariskiEquivalence (X : Scheme.{u}) :
    RLinear.TriangulatedEquivalence ℤ (DerivedCategory.CohomologyIn (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (SmallZariski X) :=
  RLinear.TriangulatedEquivalence.trans ℤ (opensEquivalence X)
    (RLinear.TriangulatedEquivalence.ofAdjunction ℤ
      (smallZariskiAdjunction X) (toSmallZariskiIsEquivalence X))

/-- The forward functor first lifts modules on `X`, then applies the canonical derived pullback. -/
@[simp]
theorem smallZariskiEquivalence_functor (X : Scheme.{u}) :
    (smallZariskiEquivalence X).functor = toOpens X ⋙ toSmallZariski X := sorry

/-- The inverse functor applies canonical derived pushforward, then reverses the universe lift. -/
@[simp]
theorem smallZariskiEquivalence_inverse (X : Scheme.{u}) :
    (smallZariskiEquivalence X).inverse =
      fromSmallZariski X ⋙ fromOpens X := sorry

/-- The quasi-coherent derived categories on the small Zariski site and its affine
Zariski subsite are canonically linearly and triangulatedly equivalent. -/
noncomputable def affineZariskiEquivalence (X : Scheme.{u}) :
    RLinear.TriangulatedEquivalence ℤ (SmallZariski X) (AffineZariski X) :=
  RLinear.TriangulatedEquivalence.symm ℤ
    (RLinear.TriangulatedEquivalence.ofAdjunction ℤ
      (affineZariskiAdjunction X) (extendFromAffineIsEquivalence X))

/-- The forward functor of the affine-Zariski equivalence is restriction to affine opens. -/
@[simp]
theorem affineZariskiEquivalence_functor (X : Scheme.{u}) :
    (affineZariskiEquivalence X).functor = restrictToAffine X := sorry

/-- The inverse functor of the affine-Zariski equivalence is extension from affine opens. -/
@[simp]
theorem affineZariskiEquivalence_inverse (X : Scheme.{u}) :
    (affineZariskiEquivalence X).inverse = extendFromAffine X := sorry

/-- The quasi-coherent derived categories on the affine Zariski and affine chaotic
sites are canonically linearly and triangulatedly equivalent. -/
noncomputable def affineTopologyEquivalence (X : Scheme.{u}) :
    RLinear.TriangulatedEquivalence ℤ (AffineZariski X) (Affine X) :=
  RLinear.TriangulatedEquivalence.symm ℤ
    (RLinear.TriangulatedEquivalence.ofAdjunction ℤ
      (affineAdjunction X) (affinePullbackIsEquivalence X))

/-- The forward functor of the affine-topology equivalence is derived pushforward. -/
@[simp]
theorem affineTopologyEquivalence_functor (X : Scheme.{u}) :
    (affineTopologyEquivalence X).functor = affinePushforward X := sorry

/-- The inverse functor of the affine-topology equivalence is derived pullback. -/
@[simp]
theorem affineTopologyEquivalence_inverse (X : Scheme.{u}) :
    (affineTopologyEquivalence X).inverse = affinePullback X := sorry

/-- Quasi-coherent cohomology on the affine chaotic site is canonically linearly and
triangulatedly equivalent to the comparison-map category `QC(X_affine, 𝒪)`. -/
noncomputable def affineQCEquivalence (X : Scheme.{u}) :
    RLinear.TriangulatedEquivalence ℤ (Affine X) (AffineQC X) :=
  RLinear.TriangulatedEquivalence.ofAdjunction ℤ
    (affineQCAdjunction X) (toAffineQCIsEquivalence X)

/-- The forward functor of the affine-`QC` equivalence is the canonical comparison. -/
@[simp]
theorem affineQCEquivalence_functor (X : Scheme.{u}) :
    (affineQCEquivalence X).functor = toAffineQC X := sorry

/-- The inverse functor of the affine-`QC` equivalence is the canonical reverse comparison. -/
@[simp]
theorem affineQCEquivalence_inverse (X : Scheme.{u}) :
    (affineQCEquivalence X).inverse = fromAffineQC X := sorry
end AlgebraicGeometry.Scheme.DerivedQCoh
