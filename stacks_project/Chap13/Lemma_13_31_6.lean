/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KInjective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.31.6

The K-injective computation theorem is a neutral pointwise-derived API.  This source file keeps
only the Stacks-facing check; downstream code should import the narrow ReasLib leaf directly.
-/

open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜] [Category.{v₂} 𝒟']
variable (F : HomotopyCategory 𝒜 (up ℤ) ⥤ 𝒟')
variable (I : CochainComplex 𝒜 ℤ) [I.IsKInjective]

/- Lemma 13.31.6: a K-injective complex computes the pointwise right-derived value of every
functor out of the homotopy category at its image in the quasi-isomorphism localization. -/
@[stacks 070Y] #check
  (Functor.KInjective.computesAt F I :
    Functor.RightDerived.ComputesAt F (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj I))

end

end CategoryTheory
