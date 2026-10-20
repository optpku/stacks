/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.CategoryTheory.Limits.Final
public import ReasLib.CategoryTheory.Filtered.Antisymmetrization.Equivalence
import StacksCheckRecall

@[expose] public section

universe u v w

variable {I : Type u} [Preorder I]

/- Remark 4.21.3 (1): the canonical partial order associated to a preorder is its quotient by
mutual comparability. -/
@[stacks 0CN1 "preorder quotient by mutual comparability"]
#check (Antisymmetrization I (· ≤ ·) : Type u)

section

variable [Nonempty I]

/- Remark 4.21.3 (2): antisymmetrization preserves nonemptiness. -/
@[stacks 0CN1 "nonemptiness descends to the antisymmetrized partial order"]
#check (Antisymmetrization.instNonempty : Nonempty (Antisymmetrization I (· ≤ ·)))

end

section

variable [IsDirectedOrder I]

/- Remark 4.21.3 (3): pairwise upper-bound directedness descends to the antisymmetrization.
Nonemptiness remains a separate hypothesis, as in mathlib's `IsDirectedOrder`. -/
@[stacks 0CN1 "upper-bound directedness descends to the antisymmetrized partial order"]
#check (Antisymmetrization.instIsDirectedOrder :
  IsDirectedOrder (Antisymmetrization I (· ≤ ·)))

end

namespace CategoryTheory

open Limits

/- Remark 4.21.3 (4): the quotient functor from a preorder to its antisymmetrization is an
equivalence of categories; the chosen representative witnesses essential surjectivity. -/
@[stacks 0CN1 "quotient functor is a categorical equivalence"]
#check (inferInstance :
  Functor.IsEquivalence
    (toAntisymmetrization_mono.functor : I ⥤ Antisymmetrization I (· ≤ ·)))

section Systems

variable {C : Type v} [Category.{w} C]

/- Remark 4.21.3 (5): precomposition by the quotient functor gives the equivalence from systems
over the antisymmetrization to systems over the original preorder. -/
@[stacks 0CN1 "equivalence of direct-system categories by quotient precomposition"]
#check ((toAntisymmetrization_mono.functor.asEquivalence.congrLeft).symm :
  (Antisymmetrization I (· ≤ ·) ⥤ C) ≌ (I ⥤ C))

/- Remark 4.21.3 (6): applying the same equivalence to opposite categories gives the inverse-system
equivalence. The preceding bridge transports this statement to the `Iᵒᵈ` presentation. -/
@[stacks 0CN1 "equivalence of inverse-system categories by quotient precomposition"]
#check (((toAntisymmetrization_mono.functor :
    I ⥤ Antisymmetrization I (· ≤ ·)).op.asEquivalence.congrLeft).symm :
  ((Antisymmetrization I (· ≤ ·))ᵒᵖ ⥤ C) ≌ (Iᵒᵖ ⥤ C))

section EquivalentStages

variable (M : I ⥤ C) {i j : I} (h : AntisymmRel (· ≤ ·) i j)

/- Remark 4.21.3 (7): for equivalent indices, the two transition maps are the two sides of
the canonical thin-category isomorphism, so every system sends them to mutually inverse
isomorphisms. -/
@[stacks 0CN1 "mutually inverse transition maps at equivalent indices"]
#check (M.mapIso (iso_of_both_ways h.1.hom h.2.hom) : M.obj i ≅ M.obj j)

end EquivalentStages

section Colimits

variable (F : Antisymmetrization I (· ≤ ·) ⥤ C)

/- Remark 4.21.3 (8): a system and its pullback along the quotient functor have colimits
simultaneously. -/
@[stacks 0CN1 "colimit existence under quotient precomposition"]
#check (Functor.Final.hasColimit_comp_iff toAntisymmetrization_mono.functor :
  HasColimit (toAntisymmetrization_mono.functor ⋙ F) ↔ HasColimit F)

variable [HasColimit F]

/- Remark 4.21.3 (9): the two colimits are canonically isomorphic. -/
@[stacks 0CN1 "canonical colimit comparison under quotient precomposition"]
#check (Functor.Final.colimitIso toAntisymmetrization_mono.functor F :
  colimit (toAntisymmetrization_mono.functor ⋙ F) ≅ colimit F)

end Colimits

section Limits

variable (F : (Antisymmetrization I (· ≤ ·))ᵒᵖ ⥤ C)

/- Remark 4.21.3 (10): an inverse system and its pullback along the quotient functor have limits
simultaneously. -/
@[stacks 0CN1 "limit existence under quotient precomposition"]
#check (Functor.Initial.hasLimit_comp_iff toAntisymmetrization_mono.functor.op :
  HasLimit (toAntisymmetrization_mono.functor.op ⋙ F) ↔ HasLimit F)

variable [HasLimit F]

/- Remark 4.21.3 (11): the two inverse limits are canonically isomorphic. -/
@[stacks 0CN1 "canonical limit comparison under quotient precomposition"]
#check (Functor.Initial.limitIso toAntisymmetrization_mono.functor.op F :
  limit (toAntisymmetrization_mono.functor.op ⋙ F) ≅ limit F)

end Limits

end Systems

end CategoryTheory
