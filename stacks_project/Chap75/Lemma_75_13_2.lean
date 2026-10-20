/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Derived.PseudoCoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction
open CategoryTheory
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

universe u

/- Lemma 75.13.2: for a scheme `X` and `E` in `D(𝒪_X)`, `E` is `m`-pseudo-coherent
if and only if `ε* E` is `m`-pseudo-coherent on the small étale site of `X`, where
`ε` is `commSmallEtaleToZariski`, the commutative universe-lifted form of
`smallEtaleToZariski` as in 75.4.0.1. -/
@[stacks 08HE] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.commSmallEtaleToZariski_isMPseudoCoherent_iff :
    ∀ {X : Scheme.{u}}
      (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) (m : ℤ),
      E.IsMPseudoCoherent m ↔
        ((commSmallEtaleToZariskiDerived X).obj E).IsMPseudoCoherent m)
