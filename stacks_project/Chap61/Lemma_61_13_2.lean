/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.WeaklyContractible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 61.13.2: let Sch_proétale be a big pro-étale site as in
Definition 61.12.7, and let T = Spec(A) be an affine object of
Sch_proétale. Then A is w-contractible if and only if T is weakly
contractible in Sch_proétale, if and only if every pro-étale covering of T
can be refined by a Zariski covering of the form T = ∐_{i=1,...,n} U_i. -/
@[stacks 098H] #check (AlgebraicGeometry.BigProetaleSite.isWContractibleRing_tfae :
  ∀ (X : AlgebraicGeometry.BigProetaleSite.{u}) {T : X.carrier}
    [IsAffine (X.toScheme.obj T)],
    List.TFAE
      [IsWContractibleRing Γ(X.toScheme.obj T, ⊤),
        X.toGrothendieck.IsWeaklyContractible T,
        Scheme.Proetale.HasFiniteCoproductZariskiRefinement (X.toScheme.obj T)])
