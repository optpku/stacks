/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.WeaklyContractible

@[expose] public section

open AlgebraicGeometry

universe u

#check (IsWContractibleRing.tfae_weaklyContractible :
  ∀ {A : Type u} [CommRing A],
    List.TFAE
      [IsWContractibleRing A,
        Scheme.proetaleTopology.IsWeaklyContractible (Spec (.of A)),
        Scheme.Proetale.HasFiniteCoproductZariskiRefinement (Spec (.of A))])
