/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Support
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 59.31.5: The support of a sheaf of rings on `Sₑₜₐₗₑ` is closed. -/
@[stacks 04FU]
#check (AlgebraicGeometry.Scheme.Etale.isClosed_etaleRingSheafSupport :
  ∀ (S : AlgebraicGeometry.Scheme.{u})
    (F : Sheaf S.smallEtaleTopology RingCat.{u}),
    IsClosed (AlgebraicGeometry.Scheme.Etale.etaleRingSheafSupport S F))
