/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.WContractible.Localization
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.11.7: if `A` is w-contractible and
`Z = V(f₁, …, fᵣ)`, then the specializing localization at
`Ideal.span (s : Set A)` is w-contractible. -/
@[stacks 0987] #check
  (IsWContractibleRing.specializing :
    ∀ {A : Type u} [CommRing A] [IsWContractibleRing A] (s : Finset A),
      IsWContractibleRing
        (Localization.specializing (1 : A) (Ideal.span (s : Set A))))

#check
  (IsWContractibleRing.specializing_of_fg :
    ∀ {A : Type u} [CommRing A] [IsWContractibleRing A] {I : Ideal A},
      I.FG → IsWContractibleRing (Localization.specializing (1 : A) I))
