/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Definition 96.4.1 (1): the associated Zariski site `X.zariskiTopology` is the
structure of site on `X` inherited from `(Sch/S)_Zar`. -/
@[stacks 06TP] #check @GroupoidsOver.zariskiTopology

/- Definition 96.4.1 (2): the associated étale site `X.etaleTopology` is the
structure of site on `X` inherited from `(Sch/S)_étale`. -/
@[stacks 06TP] #check @GroupoidsOver.etaleTopology

/- Definition 96.4.1 (3): the associated smooth site `X.smoothTopology` is the
structure of site on `X` inherited from `(Sch/S)_smooth`. -/
@[stacks 06TP] #check @GroupoidsOver.smoothTopology

/- Definition 96.4.1 (4): the associated syntomic site `X.syntomicTopology` is the
structure of site on `X` inherited from `(Sch/S)_syntomic`. -/
@[stacks 06TP] #check @GroupoidsOver.syntomicTopology

/- Definition 96.4.1 (5): the associated fppf site `X.fppfTopology` is the
structure of site on `X` inherited from `(Sch/S)_fppf`. -/
@[stacks 06TP] #check @GroupoidsOver.fppfTopology
