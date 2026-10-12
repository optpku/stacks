/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical

/-!
# Localization of naive cotangent complexes

@stack 07BR

This leaf records the canonical localization specialization of the naive
cotangent complex.  The presentation-level contraction mechanism itself is
owned by `Algebra.Extension.NaiveCotangent.Contractible`.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace Algebra.NaiveCotangent.Localization

variable {A : Type u} {Aₛ : Type v}
variable [CommRing A] [CommRing Aₛ] [Algebra A Aₛ]

/-- Lemma 10.134.10, tag `07BR`: the canonical naive cotangent complex of a localization is
homotopy equivalent to zero. -/
@[stacks 07BR]
theorem homotopyEquivZeroOfIsLocalization
    (S : Submonoid A) [IsLocalization S Aₛ] :
    Nonempty <|
      HomotopyEquiv
        (Algebra.naiveCotangent A Aₛ)
        (HomologicalComplex.zero : ChainComplex (ModuleCat Aₛ) ℕ) := sorry

end Algebra.NaiveCotangent.Localization
