/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_42_3_Exactness
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CoherentCompletion
open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 76.42.3: the completion functor (76.42.2.1)
`Coh(𝒪_X) ⟶ Coh(X, I)` is exact. -/
@[stacks 08B5] #check
  (CoherentCompletion.exact :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (I : IdealSubobject X) [IsQuasiCoherent I],
      exactFunctor (Coh X) (CoherentFormalModules X I)
        (CoherentCompletion.functor I))
