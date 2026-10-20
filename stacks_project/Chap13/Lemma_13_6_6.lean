/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.Saturation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (P : ObjectProperty D) [P.IsTriangulated]

/- Lemma 13.6.6: for a full triangulated subcategory represented by `P`, the associated Verdier
morphism property uses `P.isoClosure`; it is saturated exactly when that isomorphism closure is
stable under retracts. -/
@[stacks 05RG] #check
  (ObjectProperty.IsoClosure.TrW.saturated_iff_stableUnderRetracts P :
    P.isoClosure.trW.IsSaturatedMultiplicativeSystem ↔
      P.isoClosure.IsStableUnderRetracts)

/- If `P` is already closed under isomorphisms, the owner theorem specializes directly to
`P.trW` and retract stability of `P`. -/
section

variable [P.IsClosedUnderIsomorphisms]

#check (ObjectProperty.TrW.saturated_iff_stableUnderRetracts P :
  P.trW.IsSaturatedMultiplicativeSystem ↔ P.IsStableUnderRetracts)

end

/- A retract-stability hypothesis is sufficient for typeclass search to recover the saturated
denominator system used by all later quotient constructions. -/
section

variable [P.IsStableUnderRetracts]

#check (inferInstance : P.trW.IsSaturatedMultiplicativeSystem)

end

/- Multiplicativity and compatibility with the triangulation are canonical parts of the existing
`trW` model, not extra chapter-owned structure. -/
#check (inferInstance : P.trW.IsMultiplicative)
#check (inferInstance : P.trW.IsCompatibleWithTriangulation)

end CategoryTheory
