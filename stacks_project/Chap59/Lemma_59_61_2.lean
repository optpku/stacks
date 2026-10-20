/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.Azumaya
public import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v

namespace CSA

variable {K : Type u} [Field K]
variable (A : CSA.{u, v} K)

/- Lemma 59.61.2: for a finite central simple algebra `A` over `K`, the canonical
`K`-algebra map from `A ⊗[K] Aᵐᵒᵖ` to `Module.End K A` is an algebra isomorphism. -/
@[stacks 03R4] #check
  (CSA.mulLeftRightAlgEquiv A : A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A)

end CSA

end

-- Declarations for this item will be appended below by the statement pipeline.
