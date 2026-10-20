/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleTorsors
import StacksCheckRecall

/-!
# Lemma 61.19.7

Nonabelian first cohomology, defined as isomorphism classes of torsors,
agrees on the small étale and pro-étale sites under inverse image.
-/

universe u

/- Lemma 61.19.7: for every scheme and every sheaf of possibly noncommutative
 groups on its small étale site, inverse image induces a bijection on torsor
 isomorphism classes, the nonabelian first cohomology sets. -/
@[stacks 099X] #check
  (AlgebraicGeometry.Scheme.etaleToProEt_torsorIsoClasses_bijective :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      (G : CategoryTheory.Sheaf X.smallEtaleTopology GrpCat.{u + 1}),
      Function.Bijective (AlgebraicGeometry.Scheme.etaleToProEt_torsorIsoClasses X G))
