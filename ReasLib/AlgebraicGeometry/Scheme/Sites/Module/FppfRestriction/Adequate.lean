/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.FppfRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.FppfRestriction.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Cohomology
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules.IsAdequate

variable {S : Scheme.{u}} {τ : StandardTopology}
variable {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}

/-- An adequate module sheaf on a standard big site has a canonical realization on the big fppf site. -/
def toFppf
    (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ) :
    RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite .fppf S) where
  val := ℱ.val
  isSheaf := hℱ.isSheaf_fppf

/-- The fppf realization of an adequate module sheaf retains its underlying module presheaf. -/
theorem toFppf_val
    (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ) :
    hℱ.toFppf.val = ℱ.val := sorry

/-- An adequate module sheaf can be restricted uniformly to the small Zariski or etale site. -/
noncomputable def smallRestriction
    (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ)
    (σ : SmallStandardTopology) :
    RingedSite.ModuleCat.{u} (SmallStandardTopology.ringedSite σ S) :=
  (SmallStandardTopology.FppfRestriction.restrict σ S).obj hℱ.toFppf

/-- The uniform small-site restriction is evaluation of the canonical fppf restriction functor. -/
theorem smallRestriction_def
    (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ)
    (σ : SmallStandardTopology) :
    hℱ.smallRestriction σ =
      (SmallStandardTopology.FppfRestriction.restrict σ S).obj hℱ.toFppf := sorry

/-- Restriction through the fppf realization agrees with direct restriction to the small Zariski site. -/
theorem smallRestriction_zariski
    (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ) :
    IsIsomorphic (hℱ.smallRestriction .zariski)
      ((Scheme.SiteRestriction.bigToZariski τ S).modulePushforward.obj ℱ) := sorry

/-- Restriction through the fppf realization agrees with direct restriction to the small etale site. -/
theorem smallRestriction_etale
    (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ)
    (hτ : τ ≠ .zariski) :
    IsIsomorphic (hℱ.smallRestriction .etale)
      ((Scheme.SiteRestriction.bigToEtale τ S hτ).modulePushforward.obj ℱ) := sorry

/-- The small Zariski restriction of an adequate module sheaf is quasi-coherent. -/
theorem zariskiRestriction_isQuasicoherent
    (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ) :
    SheafOfModules.IsQuasicoherent.{u} (hℱ.smallRestriction .zariski) := sorry

/-- The small etale restriction of an adequate module sheaf is quasi-coherent. -/
theorem etaleRestriction_isQuasicoherent
    (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ) :
    SheafOfModules.IsQuasicoherent.{u} (hℱ.smallRestriction .etale) := sorry

/-- The small etale restriction is canonically the module pullback of the small Zariski restriction. -/
theorem etaleRestriction_isomorphic_zariskiPullback
    (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ) :
    IsIsomorphic (hℱ.smallRestriction .etale)
      ((Scheme.SiteRestriction.smallEtaleToZariski S).modulePullback.obj
        (hℱ.smallRestriction .zariski)) := sorry

/-- An adequate module sheaf has zero positive-degree cohomology over every affine scheme over the base. -/
theorem isZero_cohomology_of_isAffine
    (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ)
    (U : Over S) [IsAffine U.left] (q : ℕ)
    [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})] :
    IsZero
      ((Sheaf.cohomologyOverObjectFunctor (τ.overTopology S) U (q + 1)).obj
        ((SheafOfModules.toSheaf
          (StandardTopology.Big.structureSheaf τ S)).obj ℱ)) := sorry

/-- Global cohomology of the small Zariski restriction is canonically isomorphic to big-site cohomology. -/
theorem cohomology_isomorphic_restriction
    (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ)
    (q : ℕ)
    [HasSheafify (SmallStandardTopology.zariski.topology S) AddCommGrpCat.{u}]
    [HasExt.{u}
      (Sheaf (SmallStandardTopology.zariski.topology S) AddCommGrpCat.{u})]
    [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})] :
    IsIsomorphic
      ((Sheaf.functorH (SmallStandardTopology.zariski.topology S) q).obj
        ((SheafOfModules.toSheaf
          (SmallStandardTopology.ringedSite .zariski S).structureSheaf).obj
            (hℱ.smallRestriction .zariski)))
      ((Sheaf.functorH (τ.overTopology S) q).obj
        ((SheafOfModules.toSheaf
          (StandardTopology.Big.structureSheaf τ S)).obj ℱ)) := sorry

end SheafOfModules.IsAdequate
