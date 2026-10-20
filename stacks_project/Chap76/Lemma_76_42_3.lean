/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion.Exactness
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CoherentCompletion
open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 76.42.3: the completion functor (76.42.2.1)
`Coh(𝒪_X) ⟶ Coh(X, I)` is exact. -/
@[stacks 08B5] #check
  (AlgebraicGeometry.AlgebraicSpace.CoherentCompletion.exact :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (I : IdealSubobject X) [IsQuasiCoherent I],
      exactFunctor (Coh X) (CoherentFormalModules X I)
        (CoherentCompletion.functor I))
