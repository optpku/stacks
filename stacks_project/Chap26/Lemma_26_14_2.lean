module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Gluing

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/- Lemma 26.14.2: scheme gluing is the canonical specialization of locally ringed-space
gluing, and forgetting the glued scheme is canonically isomorphic to the latter construction. -/
#check GlueData
@[stacks 01JC] #check GlueData.glued
@[stacks 01JC] #check GlueData.toLocallyRingedSpaceGlueData
@[stacks 01JC] #check GlueData.isoLocallyRingedSpace

end AlgebraicGeometry.Scheme
