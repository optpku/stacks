/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.RingTheory.LocalRing.TameSymbol.Factorization
import StacksCheckRecall

universe u v

open IsLocalRing
open scoped BigOperators

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing B] [Algebra A B] [Module.Finite A B]
variable {a₁ a₂ : A}

/- 42.5.0.1: the factorization-dependent tame-symbol candidate is the product of the
residue-field norms of the signed local unit terms, weighted by the principal-quotient lengths. -/
@[stacks 0EAQ] #check (TameSymbol.Factorization.value_def :
  (D : TameSymbol.Factorization A B a₁ a₂) →
    D.value =
      D.maximals.prod fun j ↦
        (TameSymbol.residueNorm A j (D.liesOver j)
          ((-1 : j.asIdeal.ResidueFieldˣ) ^ (D.e₁ j * D.e₂ j) *
            Units.map (IsLocalRing.residue (Localization.AtPrime j.asIdeal)).toMonoidHom
                (D.u₁ j) ^ D.e₂ j *
            Units.map (IsLocalRing.residue (Localization.AtPrime j.asIdeal)).toMonoidHom
                (D.u₂ j) ⁻¹ ^ D.e₁ j)) ^ D.m j)

end
