/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Scheme gluing support

Canonical tagged facade for Mathlib scheme gluing. Basis-indexed gluing and relative-module
comparisons remain separate leaves, so importing the Chapter 26 owner does not pull in later
chapter infrastructure.
-/

@[stacks 01JC "scheme glued from scheme-valued gluing data"] #check AlgebraicGeometry.Scheme.GlueData.glued

section
@[stacks 01JC "underlying locally-ringed-space gluing data"] #check AlgebraicGeometry.Scheme.GlueData.toLocallyRingedSpaceGlueData
end

section
@[stacks 01JC "comparison with locally-ringed-space gluing"] #check AlgebraicGeometry.Scheme.GlueData.isoLocallyRingedSpace
end
