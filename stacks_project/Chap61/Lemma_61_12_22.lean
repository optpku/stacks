/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Subcanonical
import StacksCheckRecall

/-!
# Lemma 61.12.22

The pro-étale topology on each of the five pro-étale sites of a scheme is
subcanonical.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

/- Lemma 61.12.22. The five pro-étale topologies are subcanonical. -/
@[stacks 098Z] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.topologies_subcanonical :
    ∀ (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) (S : X.carrier),
      X.toGrothendieck.Subcanonical ∧
        (AlgebraicGeometry.ChosenBigProetaleSite.smallTopology X S).Subcanonical ∧
        (AlgebraicGeometry.ChosenBigProetaleSite.bigTopology X S).Subcanonical ∧
        (AlgebraicGeometry.Scheme.ProEt.affineTopology (X.toScheme.obj S)).Subcanonical ∧
        (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineTopology X S).Subcanonical)

#check (AlgebraicGeometry.Scheme.ProEt.affineTopology_subcanonical :
  ∀ (S : AlgebraicGeometry.Scheme.{u}),
    (AlgebraicGeometry.Scheme.ProEt.affineTopology S).Subcanonical)
