module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.FppfRestriction.Adequate
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 46.5.8 (restriction constructions): an adequate module sheaf has a canonical
fppf realization and small-site restrictions. -/
@[stacks 06VM] #check (SheafOfModules.IsAdequate.toFppf :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)},
      SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ →
        RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite .fppf S))
#check (SheafOfModules.IsAdequate.toFppf_val :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
      (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ),
      hℱ.toFppf.val = ℱ.val)
#check (SheafOfModules.IsAdequate.smallRestriction :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
      (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ) (σ : SmallStandardTopology),
      RingedSite.ModuleCat.{u} (SmallStandardTopology.ringedSite σ S))
#check (SheafOfModules.IsAdequate.smallRestriction_def :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
      (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ) (σ : SmallStandardTopology),
      hℱ.smallRestriction σ =
        (SmallStandardTopology.FppfRestriction.restrict σ S).obj hℱ.toFppf)
#check (SheafOfModules.IsAdequate.smallRestriction_zariski :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
      (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ),
      IsIsomorphic (hℱ.smallRestriction .zariski)
        ((Scheme.SiteRestriction.bigToZariski τ S).modulePushforward.obj ℱ))
#check (SheafOfModules.IsAdequate.smallRestriction_etale :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
      (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ) (hτ : τ ≠ .zariski),
      IsIsomorphic (hℱ.smallRestriction .etale)
        ((Scheme.SiteRestriction.bigToEtale τ S hτ).modulePushforward.obj ℱ))

/- Lemma 46.5.8 (1): the small Zariski restriction of an adequate module sheaf is
quasi-coherent. -/
@[stacks 06VM] #check
  (SheafOfModules.IsAdequate.zariskiRestriction_isQuasicoherent :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
      (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ),
      SheafOfModules.IsQuasicoherent.{u} (hℱ.smallRestriction .zariski))

/- Lemma 46.5.8 (2): the small etale restriction of an adequate module sheaf is
quasi-coherent. -/
@[stacks 06VM] #check
  (SheafOfModules.IsAdequate.etaleRestriction_isQuasicoherent :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
      (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ),
      SheafOfModules.IsQuasicoherent.{u} (hℱ.smallRestriction .etale))

/- Lemma 46.5.8 (3): the small etale restriction is the module associated to the
small Zariski restriction. -/
@[stacks 06VM] #check
  (SheafOfModules.IsAdequate.etaleRestriction_isomorphic_zariskiPullback :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
      (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ),
      IsIsomorphic (hℱ.smallRestriction .etale)
        ((Scheme.SiteRestriction.smallEtaleToZariski S).modulePullback.obj
          (hℱ.smallRestriction .zariski)))

/- Lemma 46.5.8 (4): an adequate module sheaf has zero positive-degree cohomology
over every affine scheme over the base. -/
@[stacks 06VM] #check
  (SheafOfModules.IsAdequate.isZero_cohomology_of_isAffine :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
      (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ)
      (U : Over S) [IsAffine U.left] (q : ℕ)
      [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})],
      IsZero
        ((Sheaf.cohomologyOverObjectFunctor (τ.overTopology S) U (q + 1)).obj
          ((SheafOfModules.toSheaf
            (StandardTopology.Big.structureSheaf τ S)).obj ℱ)))

/- Lemma 46.5.8 (5): the cohomology of the small Zariski restriction is canonically
isomorphic to the cohomology of the adequate module sheaf on the big site. -/
@[stacks 06VM] #check
  (SheafOfModules.IsAdequate.cohomology_isomorphic_restriction :
    ∀ {S : Scheme.{u}} {τ : StandardTopology}
      {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
      (hℱ : SheafOfModules.IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
        SheafOfModules.affineEvaluationUnderlying ℱ) (q : ℕ)
      [HasSheafify (SmallStandardTopology.zariski.topology S) AddCommGrpCat.{u}]
      [HasExt.{u}
        (Sheaf (SmallStandardTopology.zariski.topology S) AddCommGrpCat.{u})]
      [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})],
      IsIsomorphic
        ((Sheaf.functorH (SmallStandardTopology.zariski.topology S) q).obj
          ((SheafOfModules.toSheaf
            (SmallStandardTopology.ringedSite .zariski S).structureSheaf).obj
              (hℱ.smallRestriction .zariski)))
        ((Sheaf.functorH (τ.overTopology S) q).obj
          ((SheafOfModules.toSheaf
            (StandardTopology.Big.structureSheaf τ S)).obj ℱ)))
