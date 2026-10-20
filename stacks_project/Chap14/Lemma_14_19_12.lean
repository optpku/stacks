/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Limits
import StacksCheckRecall

/-!
@stack 018C

# Lemma 14.19.12 compatibility facade

The reusable owner is the objectwise coskeleton product comparison in ReasLib.  Its hypotheses
only ask for the three coskeletons and the two products occurring in the statement.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {n : ℕ}
variable (U V : SimplicialObject.Truncated C n) [HasBinaryProduct U V]
variable [U.HasCoskeleton] [V.HasCoskeleton] [(U ⨯ V).HasCoskeleton]
variable [HasBinaryProduct U.coskeleton V.coskeleton]

/- Lemma 14.19.12: the `n`-coskeleton functor preserves the binary product of `U` and `V`. -/
@[stacks 018C]
#check (Truncated.coskeleton.prod.iso U V :
  (U ⨯ V).coskeleton ≅ U.coskeleton ⨯ V.coskeleton)

/- The forward and inverse projection formulas characterize the canonical product comparison. -/
#check Truncated.coskeleton.prod.iso_hom_fst U V
#check Truncated.coskeleton.prod.iso_hom_snd U V
#check Truncated.coskeleton.prod.iso_inv_fst U V
#check Truncated.coskeleton.prod.iso_inv_snd U V

end CategoryTheory
