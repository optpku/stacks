/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalAcyclicity.LocallyConstant
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 59.93.3: A locally acyclic morphism is locally acyclic relative to every
locally constant abelian étale sheaf with prime-to-characteristic torsion
geometric stalks. -/
@[stacks 0GJR] #check
  (AlgebraicGeometry.Scheme.locallyAcyclicRelative_of_locallyAcyclic :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      [LocallyAcyclic f] [Sheaf.IsLocallyConstant F]
      [Fact (geometricStalk_isPrimeToCharTorsion F)],
      LocallyAcyclicRelative f (etaleSheafInDegreeZero F))
