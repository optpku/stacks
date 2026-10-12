/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Completion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.17.1: if completion is fully faithful on finite locally free coherent modules,
then restriction to the closed subscheme is fully faithful on finite étale schemes. -/
@[stacks 0EL8] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_fullyFaithful_of_completion :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData),
      Nonempty (CoherentCompletion.onFiniteLocallyFree I).FullyFaithful →
        Nonempty (finiteEtaleBaseChange I.subschemeι).FullyFaithful)

end AlgebraicGeometry.Scheme
