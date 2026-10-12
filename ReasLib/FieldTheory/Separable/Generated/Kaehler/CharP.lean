/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Separable.Generated.Kaehler
public import ReasLib.RingTheory.Kaehler.CharP
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Characteristic-`p` Kähler criterion for separable field extensions

This leaf records the characteristic-`p` separability criterion in terms of
the neutral prime-field Kähler base-change map.

@stack 031X
-/

@[expose] public section

universe u v

namespace Algebra.IsSeparableOver.CharP

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- Lemma 10.158.4, tag `031X`: over a field of characteristic `p`, a field
extension is Stacks-separable exactly when the prime-field Kähler base-change
map is injective. -/
@[stacks 031X]
theorem iff_mapBaseChange_injective :
    Algebra.IsSeparableOver k K ↔
      Function.Injective
        (KaehlerDifferential.CharP.primeFieldMapBaseChange (R := k) (S := K) (p := p)) := sorry

end Algebra.IsSeparableOver.CharP
