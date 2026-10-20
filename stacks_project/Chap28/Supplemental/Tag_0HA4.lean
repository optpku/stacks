/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GScheme
import StacksCheckRecall

/-!
# Characterization of G-schemes

A scheme is a G-scheme if and only if it is locally Noetherian and the
canonical map from each stalk to its maximal-adic completion is regular,
and it is equivalent to test this only at closed points.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma [Stacks 0HA4]
A scheme is a G-scheme if and only if it is locally Noetherian and all its stalk
completion maps are regular, equivalently if this holds at every closed point.
-/
@[stacks 0HA4] #check (AlgebraicGeometry.Scheme.gScheme_tfae :
  ∀ X : Scheme.{u}, List.TFAE [X.GScheme,
    IsLocallyNoetherian X ∧ ∀ x : X,
      (AlgebraicGeometry.Scheme.completedLocalMap X x).Regular,
    IsLocallyNoetherian X ∧ ∀ x : X, x ∈ closedPoints X →
      (AlgebraicGeometry.Scheme.completedLocalMap X x).Regular])
