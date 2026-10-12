/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Exactness
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.23.4: the completion functor (30.23.3.1)
`Coh(𝒪_X) ⟶ Coh(X, 𝓘)` is exact. -/
@[stacks 0881] #check
  (Scheme.CoherentCompletion.exact :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData),
      exactFunctor (RingedSpace.Coh X.toRingedSpace)
        (Scheme.CoherentFormalModules X I) (Scheme.CoherentCompletion.functor I))
