/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.InternalHomBaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Remark 21.35.12

Internal-Hom base change is categorical: it is the right mate of a square of left adjoints,
followed by the pullback/internal-Hom comparison.  ReasLib owns both the objectwise tensor-isomorphism
form and the strong-monoidal form, so the chapter does not rebuild six functors or adjunction
transposes.
-/

/- Remark 21.35.12 (08JG): the internal-Hom base-change map for an objectwise tensor
comparison. -/
@[stacks 08JG "internal-Hom base-change map"] #check
  @CategoryTheory.Adjunction.InternalHomBaseChange.map

@[stacks 08JG "internal-Hom base-change specification"] #check
  @CategoryTheory.Adjunction.InternalHomBaseChange.map_spec

/- The same construction with the tensor comparison inferred from a strong monoidal functor. -/
@[stacks 08JG "strong-monoidal internal-Hom base-change map"] #check
  @CategoryTheory.Adjunction.InternalHomBaseChange.map_monoidal

@[stacks 08JG "strong-monoidal internal-Hom base-change specification"] #check
  @CategoryTheory.Adjunction.InternalHomBaseChange.map_monoidal_spec
