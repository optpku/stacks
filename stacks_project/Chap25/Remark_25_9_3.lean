/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.InternalHom
import StacksCheckRecall

/-! # Extending a simplicial map after refinement -/

/- Remark 25.9.3 (01GT) is the specialization of the finite-subcomplex extension theorem to
`∂Δ[k] ⊆ Δ[k]`. -/
@[stacks 01GT] #check
  @CategoryTheory.Hypercovering.InternalHom.IsRefinementExtension.existsBoundary

#check @CategoryTheory.Hypercovering.InternalHom.IsRefinementExtension
#check @CategoryTheory.Hypercovering.InternalHom.IsRefinementExtension.existsOfFinite
