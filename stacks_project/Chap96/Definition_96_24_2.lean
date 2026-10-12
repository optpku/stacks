/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Definition_96_24_2_Affine
public import stacks_project.Chap96.Definition_96_24_2_Topology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Definition 96.24.2 (1): the associated affine Zariski site
`X.affineZariskiTopology` is the structure of site on `X.Affine` inherited
from `(Aff/S)_Zar`. -/
@[stacks 0H0A] #check @GroupoidsOver.affineZariskiTopology

/- Definition 96.24.2 (2): the associated affine étale site
`X.affineEtaleTopology` is the structure of site on `X.Affine` inherited from
`(Aff/S)_étale`. -/
@[stacks 0H0A] #check @GroupoidsOver.affineEtaleTopology

/- Definition 96.24.2 (3): the associated affine smooth site
`X.affineSmoothTopology` is the structure of site on `X.Affine` inherited from
`(Aff/S)_smooth`. -/
@[stacks 0H0A] #check @GroupoidsOver.affineSmoothTopology

/- Definition 96.24.2 (4): the associated affine syntomic site
`X.affineSyntomicTopology` is the structure of site on `X.Affine` inherited
from `(Aff/S)_syntomic`. -/
@[stacks 0H0A] #check @GroupoidsOver.affineSyntomicTopology

/- Definition 96.24.2 (5): the associated affine fppf site
`X.affineFppfTopology` is the structure of site on `X.Affine` inherited from
`(Aff/S)_fppf`. -/
@[stacks 0H0A] #check @GroupoidsOver.affineFppfTopology
