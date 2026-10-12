/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Approximation.Artinian
import StacksCheckRecall

@[expose] public section

/- Lemma 16.11.1: the Artinian local positive-characteristic approximation
family is owned by `Algebra.ArtinianApproximation`. -/
@[stacks 07FG]
#check @Algebra.ArtinianApproximation.System.nonempty
#check @Algebra.ArtinianApproximation.System

/- Each selected stage restores its Artinian, local, flat, and essentially
finite-type facts through the owner API. -/
#check @Algebra.ArtinianApproximation.Stage.spec
#check @Algebra.ArtinianApproximation.Stage.carrier.charP
#check @Algebra.ArtinianApproximation.System.exists_mem
