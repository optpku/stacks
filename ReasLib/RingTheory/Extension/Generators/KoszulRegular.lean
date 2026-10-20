/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Extension.Generators
public import ReasLib.RingTheory.Ideal.KoszulRegular
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Koszul-Regular Presentation Kernels

This leaf owns presentation independence of Koszul-regular kernels. The
mathematical owner is `Algebra.Generators`: both kernel ideals are derived from
finite polynomial presentations of the same algebra.

@stack 07CZ
-/

universe u v w x

namespace Algebra.Generators

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Koszul-regularity of the kernel transfers between finite polynomial presentations of the same
algebra. -/
theorem ker_isKoszulRegularIdeal_of_presentation {ι : Type w} {κ : Type x}
    [Finite ι] [Finite κ] (P : Generators R S ι) (Q : Generators R S κ)
    (hP : P.ker.IsKoszulRegularIdeal) : Q.ker.IsKoszulRegularIdeal := sorry

/-- Koszul-regularity of the kernel of a finite polynomial presentation is
independent of the chosen presentation. -/
@[stacks 07CZ "Koszul-regular presentation kernels are presentation-independent"]
theorem ker_isKoszulRegularIdeal_iff {ι : Type w} {κ : Type x}
    [Finite ι] [Finite κ] (P : Generators R S ι) (Q : Generators R S κ) :
    P.ker.IsKoszulRegularIdeal ↔ Q.ker.IsKoszulRegularIdeal := sorry

end Algebra.Generators
