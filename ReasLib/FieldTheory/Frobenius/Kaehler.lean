/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Frobenius.Compositum
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Frobenius composita and Kähler differentials

@stack 07P2

This leaf isolates the generation criterion underlying the differential characterization of a
p-basis. It depends on the Frobenius compositum and the universal derivation, but not on the
p-independence predicate.
-/

@[expose] public section

universe u v w

namespace FieldExtension.Frobenius.Kaehler

open KaehlerDifferential

variable (p : ℕ) (k : Type u) {K : Type v}
variable [Field k] [Field K] [Algebra k K] [Fact p.Prime] [CharP K p]
variable {ι : Type w}

/-- An intermediate field containing all p-th powers is the whole field when its relative Kähler
differential module is subsingleton.  The `Subsingleton` fact is explicit so this bridge does not
install a temporary ambient instance in downstream statements. -/
@[stacks 07P2 "Frobenius containment and vanishing differentials"]
theorem eq_top_of_subfield_le_of_subsingleton (L : IntermediateField k K)
    (hF : subfield p K ≤ L.toSubfield) (hΩ : Subsingleton Ω[K⁄L]) : L = ⊤ := sorry
/- Proof strategy: obtain the exponent-one purely inseparable structure from
`FieldExtension.Frobenius.isPurelyInseparable_of_subfield_le L hF`.  A dedicated derivation argument
shows that any nontrivial element of this extension contributes a nonzero relative differential;
`hΩ` therefore forces the algebra map from `L` to be surjective and hence `L = ⊤`.  This avoids the
false generic implication from vanishing differentials to separability without finite type. -/

/-- Generation over the Frobenius compositum is equivalent to spanning the relative Kähler module
by the corresponding universal differentials. -/
@[stacks 07P2 "Frobenius-compositum generation via Kähler differentials"]
theorem adjoin_eq_top_iff_span_eq_top (x : ι → K) :
    IntermediateField.adjoin (compositum p k K) (Set.range x) = ⊤ ↔
      Submodule.span K (Set.range (D k K ∘ x)) = ⊤ := sorry
/- Proof strategy: for the forward implication, close differential-span membership under the field
operations generating the adjoin and use `KaehlerDifferential.span_range_derivation`. Conversely,
map to differentials over the generated intermediate field; the spanning hypothesis makes that
module trivial, then apply `eq_top_of_subfield_le_of_subsingleton`. -/

/-- Generation over the Frobenius compositum makes the corresponding differentials span. -/
@[stacks 07P2 "differential spanning from Frobenius generation"]
theorem span_eq_top_of_adjoin_eq_top (x : ι → K)
    (hx : IntermediateField.adjoin (compositum p k K) (Set.range x) = ⊤) :
    Submodule.span K (Set.range (D k K ∘ x)) = ⊤ :=
  (adjoin_eq_top_iff_span_eq_top p k x).mp hx
/- Proof strategy: apply the forward direction of `adjoin_eq_top_iff_span_eq_top`. -/

/-- A spanning family of universal differentials generates over the Frobenius compositum. -/
@[stacks 07P2 "Frobenius generation from differential spanning"]
theorem adjoin_eq_top_of_span_eq_top (x : ι → K)
    (hx : Submodule.span K (Set.range (D k K ∘ x)) = ⊤) :
    IntermediateField.adjoin (compositum p k K) (Set.range x) = ⊤ :=
  (adjoin_eq_top_iff_span_eq_top p k x).mpr hx
/- Proof strategy: apply the reverse direction of `adjoin_eq_top_iff_span_eq_top`. -/

end FieldExtension.Frobenius.Kaehler
