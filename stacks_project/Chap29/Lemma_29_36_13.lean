/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import StacksCheckRecall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]

/- Lemma 29.36.13: an étale morphism is open. -/
@[stacks 03WT] #check (AlgebraicGeometry.Scheme.Hom.isOpenMap f : IsOpenMap f.base)

end AlgebraicGeometry
