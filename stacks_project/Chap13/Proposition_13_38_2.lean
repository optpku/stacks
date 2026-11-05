/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability.SmallSet
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 13.38.2

Brown representability for compactly generated triangulated categories is exposed through the
neutral small-coproduct functor-level API.
-/

namespace CategoryTheory.Functor.Brown.SmallSet

/- Proposition 13.38.2 (`0A8G`): the left-adjoint criterion. -/
@[stacks 0A8G] #check @isLeftAdjoint_ofCompactGeneration

/- Exactness of a Brown right adjoint. -/
#check @hasTriangulatedRightAdjoint_ofCompactGeneration

end CategoryTheory.Functor.Brown.SmallSet
