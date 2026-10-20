/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveLine

section Source

variable (k : Type u) [Field k]

/- Example 26.21.8: the structure morphism of `ℙ¹_k` is separated. -/
@[stacks 01KQ] #check toSpec_isSeparated k

end Source

section Generalization

variable (R : Type u) [CommRing R]

#check toSpec_isSeparated R

end Generalization

end AlgebraicGeometry.ProjectiveLine
