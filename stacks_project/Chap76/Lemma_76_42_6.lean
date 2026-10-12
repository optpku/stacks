/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import stacks_project.Chap76.Lemma_76_42_6_Hom
import stacks_project.Chap76.Lemma_76_42_6_Instances
import stacks_project.Chap76.Lemma_76_42_6_ProperOver

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CoherentCompletion
open AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 76.42.6 (1): in Situation 76.42.5, if F and G are coherent 𝒪_X-modules
and the intersection of their supports is proper over Spec(A), then the map
Hom(F, G) ⟶ Hom(F^∧, G^∧) coming from 76.42.2.1 is a bijection. -/
@[stacks 08B9] #check homMap_bijective

/- Lemma 76.42.6 (2): in particular, the restricted functor 76.42.5.1 is full. -/
@[stacks 08B9] #check instFull_coherentProperSupportCompletionFunctor

/- Lemma 76.42.6 (3): in particular, the restricted functor 76.42.5.1 is faithful. -/
@[stacks 08B9] #check instFaithful_coherentProperSupportCompletionFunctor
