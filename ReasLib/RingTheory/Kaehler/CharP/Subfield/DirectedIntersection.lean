module

public import ReasLib.RingTheory.Kaehler.CharP.Subfield
public import ReasLib.FieldTheory.Frobenius.Subfield
import ReasLib.FieldTheory.PBasis.Kaehler
import ReasLib.FieldTheory.Subfield.RationalPoints.DirectedIntersection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed intersections of prime-field Kähler kernels

@stack 07P4

This leaf owns the reusable kernel-intersection statement for the canonical maps from prime-field
Kähler differentials to differentials relative to a directed family of subfields.  The finite
p-basis and coordinate arguments are proof infrastructure, not public data.
-/

@[expose] public section

universe u v

namespace KaehlerDifferential.CharP.SubfieldMap

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]

/-- Lemma 15.46.4 (1): the kernels of the subfield-relative prime-field maps have zero infimum
when the subfields are nonempty, downward directed, and intersect in the Frobenius subfield. -/
@[stacks 07P4 "Lemma 15.46.4 (1): directed Kähler kernel intersection"]
theorem iInf_ker_eq_bot {A : Type v} (h_nonempty : Nonempty A)
    (Kα : A → Subfield K)
    (h_inter : FieldExtension.Frobenius.subfield p K = ⨅ α, Kα α)
    (h_directed : Directed (· ≥ ·) Kα) :
    (⨅ α, LinearMap.ker (map (Kα α))) = ⊥ := sorry
/- Proof strategy: use the canonical p-basis differential criterion, reduce every kernel element to
a finite coefficient relation, and apply `Submodule.RationalPoints.ne_bot_iff_of_eq_iInf` to the
directed family.  The p-basis and coordinate owners are imported directly; the remaining reduction
is the deferred proposition proof. -/

end KaehlerDifferential.CharP.SubfieldMap
