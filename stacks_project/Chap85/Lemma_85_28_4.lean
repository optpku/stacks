/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.SimplicialScheme.QCoh.Cech

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 85.28.4. For a morphism of schemes admitting a section, pullback to its
Čech nerve induces an equivalence on quasi-coherent modules. -/
@[stacks 07TL] #check
  (AlgebraicGeometry.SimplicialObject.QCoh.cechPullback_isEquivalence :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsSplitEpi f],
      (AlgebraicGeometry.SimplicialObject.QCoh.cechPullback f).IsEquivalence)
