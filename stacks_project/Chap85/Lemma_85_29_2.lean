/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Zariski
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 85.29.2
Let `S` be a scheme. Let `(U, R, s, t, c)` be a groupoid scheme over `S`. Let `X` be the
simplicial scheme over `S` constructed in Lemma 85.29.1. Then the category of quasi-coherent
modules on `(U, R, s, t, c)` is equivalent to the category of quasi-coherent modules on
`X_Zar`. -/
@[stacks 07TP] #check
  (AlgebraicGeometry.GroupoidScheme.quasiCoherentZariskiEquivalence :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      G.QCoh ≌ AlgebraicGeometry.SimplicialObject.QCoh G.simplicialScheme)
