/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.EnoughPoints
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u v

/- Lemma 61.18.1 (1): the pro-étale site Sch_proétale has enough points. -/
@[stacks 0992] #check (AlgebraicGeometry.Scheme.hasEnoughPoints_proetale :
  CategoryTheory.GrothendieckTopology.HasEnoughPoints.{u + 2}
    (proetaleTopology : CategoryTheory.GrothendieckTopology Scheme.{u}))

/- Lemma 61.18.1 (2): the pro-étale site S_proétale has enough points. -/
@[stacks 0992] #check (AlgebraicGeometry.Scheme.ProEt.hasEnoughPoints :
  ∀ S : Scheme.{u},
    CategoryTheory.GrothendieckTopology.HasEnoughPoints.{u + 2} (ProEt.topology S))

/- Lemma 61.18.1 (3): the pro-étale site (Sch/S)_proétale has enough points. -/
@[stacks 0992] #check (AlgebraicGeometry.Scheme.hasEnoughPoints_proetaleOver :
  ∀ S : Scheme.{u},
    CategoryTheory.GrothendieckTopology.HasEnoughPoints.{u + 2} (proetaleTopology.over S))

/- Lemma 61.18.1 (4): the pro-étale site S_affine,proétale has enough points. -/
@[stacks 0992] #check (AlgebraicGeometry.Scheme.ProEt.hasEnoughPoints_affine :
  ∀ S : Scheme.{u},
    CategoryTheory.GrothendieckTopology.HasEnoughPoints.{u + 2} (ProEt.affineTopology S))

/- Lemma 61.18.1 (5): the pro-étale site (Aff/S)_proétale has enough points. -/
@[stacks 0992] #check (AlgebraicGeometry.ChosenBigProetaleSite.hasEnoughPoints_bigAffine :
  ∀ (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier),
    CategoryTheory.GrothendieckTopology.HasEnoughPoints.{max (max u v + 1) (v + 1)}
      (ChosenBigProetaleSite.bigAffineTopology X S))
