/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential.Resolution
import StacksCheckRecall

/-!
# Lemma 15.88.7

@stack 091F
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.88.7 (091F): every derived object over a sequential varying-ring system has a
cochain representative whose evaluated successor maps are epimorphisms.  The generic owner is
specialized to `F = sequentialRingSystem A ρ` for the source family. -/
@[stacks 091F "representative with epimorphic stage transitions"]
#check @SequentialInverseSystem.ModuleSystem.existsCochainRepresentativeWithEpiTransitions

#check @SequentialInverseSystem.sequentialRingSystem
#check @SequentialInverseSystem.cochainEvaluationStep

end
