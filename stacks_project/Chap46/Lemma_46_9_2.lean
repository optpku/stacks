/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.AssociatedExt
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe w u

/- Lemma 46.9.2 -/
@[stacks 0709]
#check (ModuleCat.PureExt.comparisonIsIso :
    ∀ (τ : StandardTopology) (A : CommRingCat.{u})
      [Abelian (ModuleValuedFunctor.TensorAdeq A)]
      [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)]
      [Abelian (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (Opposite.op A))))]
      [HasExt.{w} (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (Opposite.op A))))]
      [@Functor.Additive
        (ModuleValuedFunctor.TensorAdeq A)
        (RingedSite.ModuleCat.{u}
          (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (Opposite.op A))))
        _ _ Abelian.toPreadditive Abelian.toPreadditive
        (SheafOfModules.AffineAdeq.realization τ A)]
      [PreservesFiniteLimits (SheafOfModules.AffineAdeq.realization τ A)]
      [PreservesFiniteColimits (SheafOfModules.AffineAdeq.realization τ A)]
      (i : ℕ), IsIso (ModuleCat.PureExt.comparison τ A i))
