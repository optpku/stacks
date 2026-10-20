/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.EtaleComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.EtaleComparison
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 75.4.2: for a scheme `X`, the exact pullback `ε^*` along
`ε : (X_étale, 𝒪_étale) ⟶ (X_Zar, 𝒪_X)` induces an equivalence
`Scheme.DerivedQCoh X ⥤ DerivedQCoh.SmallEtale X`. -/
@[stacks 071Q] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.epsilonStar_isEquivalence :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      Functor.IsEquivalence (AlgebraicGeometry.Scheme.DerivedQCoh.epsilonStar X))
