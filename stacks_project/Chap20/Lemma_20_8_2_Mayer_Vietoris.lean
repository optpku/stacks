/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.MayerVietoris
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace.Module.Cohomology.MayerVietoris

/- Lemma 20.8.2 (01EB): the Mayer--Vietoris exact sequence for an `𝒪_X`-module on a two-open
cover, together with its coefficient-module functoriality. -/
@[stacks 01EB "Mayer--Vietoris exact sequence for module cohomology"]
#check @augmented_exact

/- The five-arrow core and its canonical concrete data are reusable companions of the augmented
statement above. -/
@[stacks 01EB "Mayer--Vietoris five-arrow core"]
#check @sequence_exact

@[stacks 01EB "functorial Mayer--Vietoris sequence"]
#check @augmentedFunctor

#check @AlgebraicGeometry.RingedSpace.Module.Cohomology.MayerVietoris.sequence
#check @sequenceMap
#check @sequenceMap_id
#check @sequenceMap_comp
#check @functor
#check @augmented
