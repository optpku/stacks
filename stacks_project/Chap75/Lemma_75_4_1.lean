/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Zariski.Flat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 75.4.1 (1): the morphism ε : (X_étale, 𝒪_étale) ⟶ (X_Zar, 𝒪_X)
of 75.4.0.1 is a flat morphism of ringed sites. -/
@[stacks 08H8] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski_isFlat :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      RingedSite.Hom.IsFlat.{u}
        (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski S))

/- Lemma 75.4.1 (2): the functor ε* : Mod(𝒪_X) ⟶ Mod(𝒪_étale) is exact. -/
@[stacks 08H8] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski_modulePullback_exact :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      CategoryTheory.exactFunctor
        (RingedSite.ModuleCat.{u}
          (AlgebraicGeometry.Scheme.Zariski.Small.ringedSite X))
        (RingedSite.ModuleCat.{u}
          (AlgebraicGeometry.Scheme.Etale.Small.ringedSite X))
        (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski X).modulePullback.{u})

/- Lemma 75.4.1: if ε* ℱ = 0, then ℱ = 0. -/
@[stacks 08H8] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski_modulePullback_reflects_isZero :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      (F : RingedSite.ModuleCat.{u}
        (AlgebraicGeometry.Scheme.Zariski.Small.ringedSite X)),
      IsZero
        ((AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski X).modulePullback.{u}.obj F) →
        IsZero F)

/- The kernel of module pullback consists of zero objects. -/
#check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski_modulePullback_kernel_le_isZero :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski X).modulePullback.{u}.kernel ≤
        IsZero)

/- A module vanishes if and only if its pullback vanishes. -/
#check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski_modulePullback_isZero_iff :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      (F : RingedSite.ModuleCat.{u}
        (AlgebraicGeometry.Scheme.Zariski.Small.ringedSite X)),
      IsZero
        ((AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski X).modulePullback.{u}.obj F) ↔
        IsZero F)
