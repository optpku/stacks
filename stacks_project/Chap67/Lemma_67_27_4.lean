/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_27_2
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace MorphismProperty

/- Lemma 67.27.4 (1): A base change of a quasi-finite morphism is quasi-finite. -/
@[stacks 03XL] #check
  (quasiFinite_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, IsStableUnderBaseChange
      (@QuasiFinite S : MorphismProperty (AlgebraicSpace S)))

/- Lemma 67.27.4 (2): A base change of a locally quasi-finite morphism is
locally quasi-finite. -/
@[stacks 03XL] #check
  (locallyQuasiFinite_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, IsStableUnderBaseChange
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)))

#check QuasiFinite.pullback_snd
#check LocallyQuasiFinite.pullback_snd
