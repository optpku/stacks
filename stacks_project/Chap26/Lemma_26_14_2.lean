/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
