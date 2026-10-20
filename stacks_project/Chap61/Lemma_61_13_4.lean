/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.EnoughWeaklyContractible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u v

/- Lemma 61.13.4 (1): the pro-étale site S_proétale has enough affine
quasi-compact weakly contractible objects. -/
@[stacks 0990] #check
  (AlgebraicGeometry.Scheme.ProEt.hasEnough_isAffine_isWeaklyContractible :
    ∀ S : Scheme.{u}, (ProEt.topology S).HasEnoughObjectsWithProperty
      (fun U ↦ IsAffine U.left ∧ (ProEt.topology S).IsWeaklyContractible U))

/- Lemma 61.13.4 (2): the pro-étale site (Sch/S)_proétale has enough affine
quasi-compact weakly contractible objects. -/
@[stacks 0990] #check
  (AlgebraicGeometry.Scheme.hasEnough_isAffine_isWeaklyContractible_proetaleOver :
    ∀ S : Scheme.{u}, (proetaleTopology.over S).HasEnoughObjectsWithProperty
      (fun U ↦ IsAffine U.left ∧ (proetaleTopology.over S).IsWeaklyContractible U))

/- Lemma 61.13.4 (3): the pro-étale site S_affine,proétale has enough weakly
contractible objects. -/
@[stacks 0990] #check
  (AlgebraicGeometry.Scheme.ProEt.hasEnough_isWeaklyContractible_affine :
    ∀ S : Scheme.{u}, (ProEt.affineTopology S).HasEnoughObjectsWithProperty
      (ProEt.affineTopology S).IsWeaklyContractible)

/- Lemma 61.13.4 (4): the pro-étale site (Aff/S)_proétale has enough weakly
contractible objects. -/
@[stacks 0990] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.hasEnough_isWeaklyContractible_bigAffine :
    ∀ (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier),
      (ChosenBigProetaleSite.bigAffineTopology X S).HasEnoughObjectsWithProperty
        (ChosenBigProetaleSite.bigAffineTopology X S).IsWeaklyContractible)

/- Lemma 61.13.4 (5): if S is affine, the pro-étale site S_app has enough
weakly contractible objects. -/
@[stacks 0990] #check
  (AlgebraicGeometry.Scheme.ProEt.hasEnough_isWeaklyContractible_affineIndEtale :
    ∀ (S : Scheme.{u}) [IsAffine S],
      (ProEt.affineIndEtaleTopology S).HasEnoughObjectsWithProperty
        (ProEt.affineIndEtaleTopology S).IsWeaklyContractible)
