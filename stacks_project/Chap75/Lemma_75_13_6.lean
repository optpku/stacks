/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 75.13.6 (1): if `E` is `m`-pseudo-coherent in `D(𝒪_X)`, then `H^i(E)` is a
quasi-coherent `𝒪_X`-module for `i > m`. -/
@[stacks 08JL] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.PseudoCoherent.higherCohomology_isQuasicoherent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X} {m i : ℤ},
      IsMPseudoCoherent X E m → m < i →
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E).IsQuasicoherent)

/- Lemma 75.13.6 (2): if `E` is pseudo-coherent in `D(𝒪_X)`, then `E` is an object of
`D_QCoh(𝒪_X)`. -/
@[stacks 08JL] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.PseudoCoherent.derivedQuasiCoherentModuleProperty :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X},
      IsPseudoCoherent X E → derivedQuasiCoherentModuleProperty X E)
