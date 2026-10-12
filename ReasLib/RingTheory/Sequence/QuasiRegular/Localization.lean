/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import ReasLib.Algebra.Module.LocalizedModule.Kernel
public import ReasLib.RingTheory.Sequence.QuasiRegular.Finite

/-!
# Localization of Quasi-Regular Sequences

@stack 061Q

The core API identifies localized quasi-regularity with vanishing of the
localized comparison kernel.  The finite Noetherian specialization then
spreads quasi-regularity from a prime localization to one principal open.
-/

@[expose] public section

universe u v

namespace RingTheory.Sequence.IsQuasiRegular

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Tag `061Q`: quasi-regularity after localization is equivalent to the
localized comparison kernel being trivial. -/
@[stacks 061Q "localized quasi-regularity criterion"]
theorem localized_iff (T : Submonoid R) {rs : List R} :
    IsQuasiRegular (LocalizedModule T M)
        (rs.map (algebraMap R (Localization T))) ↔
      Subsingleton
        (LocalizedModule T (QuasiRegular.comparisonKernel (M := M) rs)) := sorry

/-- Lemma 10.69.4, tag `061Q`: if a sequence is quasi-regular after
localizing at `p`, it is quasi-regular on some principal open containing `p`. -/
@[stacks 061Q]
theorem exists_away_of_atPrime [IsNoetherianRing R] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] {rs : List R}
    (hrs : IsQuasiRegular (LocalizedModule.AtPrime p M)
      (rs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ g : R, g ∉ p ∧
      IsQuasiRegular (LocalizedModule.Away g M)
        (rs.map (algebraMap R (Localization.Away g))) := sorry

end RingTheory.Sequence.IsQuasiRegular
