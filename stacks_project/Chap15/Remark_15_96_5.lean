/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Reduction

@[expose] public section

/-!
# Remark 15.96.5: reduction of the Berthelot-Ogus eta complex

@stack 0F7S
-/

open scoped nonZeroDivisors
open CochainComplex.BerthelotOgus.Int.Reduction

noncomputable section

universe u v

section

variable {A : Type u} [CommRing A]
variable (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
variable (hf : f ∈ nonZeroDivisors A)
variable (hK : CochainComplex.BerthelotOgus.Int.IsTermwiseTorsionFree f K)

/- The reduced integer-indexed eta complex used in Remark 15.96.5. -/
#check complex f K hK

/- Remark 15.96.5, tag `0F7S` (1): the divided map `t` to cycles modulo `f`. -/
@[stacks 0F7S "eta reduction maps to cycles modulo f"]
#check toCycles f K i hK

/- Remark 15.96.5, tag `0F7S` (2): the explicit map `s` from outgoing boundaries. -/
@[stacks 0F7S "outgoing boundaries map into eta reduction"]
#check boundary f K i hK

/- Remark 15.96.5, tag `0F7S` (3): the explicit map `s'` from incoming boundaries. -/
@[stacks 0F7S "incoming boundaries map into eta reduction"]
#check previousBoundary f K i hK

/- The middle vertical map `(s, s')` in the diagram of Remark 15.96.5. -/
#check boundaryPair f K i hK

/- Remark 15.96.5, tag `0F7S`: the commutative diagram has exact rows. -/
@[stacks 0F7S "exact boundary diagram for the reduced eta complex"]
#check boundaryDiagram_hasExactRows f K i hf hK

/- The quotient map in the lower row lands canonically in ambient homology. -/
#check toHomology f K i hK

end
