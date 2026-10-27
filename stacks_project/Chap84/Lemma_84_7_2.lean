/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.EtaleFppfComparison

/-!
# Lemma 84.7.2

For a quasi-coherent module on an algebraic space, the canonical maps
`π_X^* F ⟶ Rε_{X,*}(a_X^* F)` and `F ⟶ Ra_{X,*}(a_X^* F)` are isomorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Fppf
open AlgebraicGeometry.AlgebraicSpace.AssociatedModule
open RingedSite.Hom

universe u

/- Lemma 84.7.2 (1): the canonical derived comparison is an isomorphism. -/
@[stacks 0DGP] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.piPullbackToEpsilonDerived_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent],
    IsIso (piPullbackToEpsilonDerived F))

/- Lemma 84.7.2 (2): the canonical derived comparison is an isomorphism. -/
@[stacks 0DGP] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.toADerived_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent],
    IsIso (toADerived F))
