/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.UniverseLift
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules

/-- The adequate-module property used degreewise in `DerivedAdeq S τ`. -/
abbrev adequateProperty (S : Scheme.{u}) (τ : StandardTopology) :
    ObjectProperty
      (RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ S)) :=
  @IsAdequateWith S τ ModuleValuedFunctor.tensorExtensionUnderlyingLifted
    (@affineEvaluationUnderlyingLifted S τ)

/-- The degreewise adequate object property on the unbounded derived module category. -/
abbrev derivedAdequateProperty (S : Scheme.{u}) (τ : StandardTopology) :
    ObjectProperty
      (RingedSite.Hom.ModuleDerived.{u + 1}
        (StandardTopology.Big.ringedSite τ S)) :=
  @DerivedCategory.cohomologyIn _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
      (StandardTopology.Big.ringedSite τ S))
    (adequateProperty S τ)

/-- The unbounded derived category of modules on the big `τ`-site of `S` whose
cohomology modules are adequate. -/
abbrev DerivedAdeq (S : Scheme.{u}) (τ : StandardTopology) :=
  (derivedAdequateProperty S τ).FullSubcategory

namespace DerivedAdeq

/-- Every homology module of an object of `DerivedAdeq S τ` is adequate. -/
theorem homology_isAdequate (S : Scheme.{u}) (τ : StandardTopology)
    (K : DerivedAdeq S τ) (n : ℤ) :
    IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
      affineEvaluationUnderlyingLifted
      ((@DerivedCategory.homologyFunctor
        (RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ S)) _ _
        (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
          (StandardTopology.Big.ringedSite τ S)) n).obj K.obj) := sorry

end DerivedAdeq

end SheafOfModules

namespace AlgebraicGeometry.StandardTopology.Big

/-- The identity-on-objects morphism from the big fppf ringed site to the big `τ`-ringed site. -/
noncomputable def toFppfHom (τ : StandardTopology) (S : Scheme.{u}) :
    RingedSite.Hom (ringedSite .fppf S) (ringedSite τ S) :=
  Scheme.Site.ringedHom (τ.overTopology S) (StandardTopology.fppf.overTopology S)
    (Over.forget S) (Over.forget S) (𝟭 (Over S)) (𝟙 (Over.forget S))
    (structurePresheaf_isSheaf τ S) (structurePresheaf_isSheaf .fppf S)

/-- The base functor of `toFppfHom τ S` is the identity of `Over S`. -/
theorem toFppfHom_base (τ : StandardTopology) (S : Scheme.{u}) :
    (toFppfHom τ S).base = 𝟭 (Over S) := sorry

/-- Module direct image along `toFppfHom τ S` has its canonical inverse-image left adjoint. -/
noncomputable def toFppfHom_modulePushforwardIsRightAdjoint
    (τ : StandardTopology) (S : Scheme.{u}) :
    ((toFppfHom τ S).modulePushforward.{u + 1}).IsRightAdjoint := sorry

/-- Module inverse image along `toFppfHom τ S` admits its canonical unbounded left-derived
functor. -/
noncomputable def toFppfHom_modulePullbackHasLeftDerived
    (τ : StandardTopology) (S : Scheme.{u}) :
    Functor.HasLeftDerivedFunctor
      (@RingedSite.Hom.modulePullbackToDerived.{u + 1} _ _ (toFppfHom τ S) inferInstance
        (toFppfHom_modulePushforwardIsRightAdjoint τ S))
      (RingedSite.Hom.ModuleQis.{u + 1} (ringedSite τ S)) := sorry

/-- The topology-change morphism `toFppfHom τ S` is flat on module sheaves. -/
noncomputable def toFppfHom_isFlat (τ : StandardTopology) (S : Scheme.{u}) :
    @RingedSite.Hom.IsFlat.{u + 1, u + 1, u, u + 1, u, u} _ _
      (toFppfHom τ S) (toFppfHom_modulePushforwardIsRightAdjoint τ S) := sorry

end AlgebraicGeometry.StandardTopology.Big

namespace SheafOfModules.DerivedAdeq

/-- Pullback from the big `τ`-site to the big fppf site preserves adequacy. -/
theorem toFppf_mapsAdequate (S : Scheme.{u}) (τ : StandardTopology) :
      SheafOfModules.adequateProperty S τ ≤
      (SheafOfModules.adequateProperty S .fppf).inverseImage
        (@RingedSite.Hom.modulePullback.{u + 1} _ _
          (StandardTopology.Big.toFppfHom τ S)
          (StandardTopology.Big.toFppfHom_modulePushforwardIsRightAdjoint τ S)) := sorry

/-- Pullback from adequate modules on the big `τ`-site to adequate modules on the big fppf
site. -/
noncomputable abbrev toFppfAdeq (S : Scheme.{u}) (τ : StandardTopology) :
    (SheafOfModules.adequateProperty S τ).FullSubcategory ⥤
      (SheafOfModules.adequateProperty S .fppf).FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict
    (@RingedSite.Hom.modulePullback.{u + 1} _ _
      (StandardTopology.Big.toFppfHom τ S)
      (StandardTopology.Big.toFppfHom_modulePushforwardIsRightAdjoint τ S))
    (toFppf_mapsAdequate S τ)

/-- Underived pullback along `toFppfHom τ S`, restricted to adequate modules, is an
equivalence. -/
instance toFppfAdeq_isEquivalence (S : Scheme.{u}) (τ : StandardTopology) :
    Functor.IsEquivalence (toFppfAdeq S τ) := sorry

/-- Derived pullback from the big `τ`-site to the big fppf site preserves degreewise
adequacy. -/
theorem toFppf_mapsDerivedAdequate (S : Scheme.{u}) (τ : StandardTopology) :
    SheafOfModules.derivedAdequateProperty S τ ≤
      (SheafOfModules.derivedAdequateProperty S .fppf).inverseImage
        (@RingedSite.Hom.modulePullbackDerived.{u + 1} _ _
          (StandardTopology.Big.toFppfHom τ S) inferInstance inferInstance
          (StandardTopology.Big.toFppfHom_modulePushforwardIsRightAdjoint τ S)
          (StandardTopology.Big.toFppfHom_modulePullbackHasLeftDerived τ S)) := sorry

/-- The canonical derived pullback from adequate-cohomology complexes on the big `τ`-site
to adequate-cohomology complexes on the big fppf site. -/
noncomputable abbrev toFppf (S : Scheme.{u}) (τ : StandardTopology) :
    DerivedAdeq S τ ⥤ DerivedAdeq S .fppf :=
  ObjectProperty.FullSubcategory.restrict
    (@RingedSite.Hom.modulePullbackDerived.{u + 1} _ _
      (StandardTopology.Big.toFppfHom τ S) inferInstance inferInstance
      (StandardTopology.Big.toFppfHom_modulePushforwardIsRightAdjoint τ S)
      (StandardTopology.Big.toFppfHom_modulePullbackHasLeftDerived τ S))
    (toFppf_mapsDerivedAdequate S τ)

/-- `toFppf S τ` is the generic restricted derived pullback along the canonical
identity-on-objects morphism of ringed sites. -/
theorem toFppf_def (S : Scheme.{u}) (τ : StandardTopology) :
    toFppf S τ =
      ObjectProperty.FullSubcategory.restrict
        (@RingedSite.Hom.modulePullbackDerived.{u + 1} _ _
          (StandardTopology.Big.toFppfHom τ S) inferInstance inferInstance
          (StandardTopology.Big.toFppfHom_modulePushforwardIsRightAdjoint τ S)
          (StandardTopology.Big.toFppfHom_modulePullbackHasLeftDerived τ S))
        (toFppf_mapsDerivedAdequate S τ) := sorry

/-- The canonical derived pullback from any standard big site to the big fppf site is an
equivalence on complexes with adequate cohomology. -/
noncomputable instance toFppf_isEquivalence (S : Scheme.{u}) (τ : StandardTopology) :
    Functor.IsEquivalence (toFppf S τ) := sorry

end SheafOfModules.DerivedAdeq

end
