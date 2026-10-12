/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.PBasis
public import ReasLib.FieldTheory.Frobenius.Kaehler
import ReasLib.FieldTheory.PBasis.Derivation
import ReasLib.RingTheory.Kaehler.Dual
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kähler criteria for p-bases

@stack 07P2

The differential family is named data, and the canonical `Module.Basis.mk` construction is exposed
without hiding a chosen carrier or representative.  The characterization laws remain
proposition-valued.
-/

@[expose] public section

universe u v w

namespace FieldExtension.PBasis

open KaehlerDifferential

section DifferentialFamily

variable (k : Type u) {K : Type v} [Field k] [Field K] [Algebra k K]
variable {ι : Type w}

/-- The family of universal differentials attached to a family of elements of `K`. -/
@[stacks 07P2 "universal differential family of a p-basis candidate"]
noncomputable abbrev differentials (x : ι → K) : ι → Ω[K⁄k] := D k K ∘ x

end DifferentialFamily

section IndependenceCriterion

variable (p : ℕ) (k : Type u) {K : Type v}
variable [Field k] [Field K] [Algebra k K] [Fact p.Prime] [CharP K p]
variable {ι : Type w}

/-- Lemma 15.46.2, equivalence (1)-(2): p-independence is detected by linear independence of
universal differentials. -/
@[stacks 07P2 "Lemma 15.46.2, equivalence (1)-(2): differential criterion"]
theorem isIndependent_iff_differentials (x : ι → K) :
    IsIndependent p k x ↔ LinearIndependent K (differentials k x) :=
  (isIndependent_iff_dual_derivations p k x).trans
    (KaehlerDifferential.linearIndependent_iff_dual_derivations x).symm
/- Proof strategy: combine `isIndependent_iff_dual_derivations` with
`KaehlerDifferential.linearIndependent_iff_dual_derivations`, which identifies the same dual
derivation family with linear independence of the universal differentials. -/

end IndependenceCriterion

section IndependentAPI

variable {p : ℕ} {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K] [Fact p.Prime] [CharP K p]
variable {ι : Type w}

/-- A p-independent family has linearly independent universal differentials. -/
@[stacks 07P2 "differential independence from p-independence"]
theorem IsIndependent.linearIndependent_differentials {x : ι → K}
    (hx : IsIndependent p k x) : LinearIndependent K (differentials k x) :=
  (isIndependent_iff_differentials p k x).mp hx
/- Proof strategy: apply the forward direction of `isIndependent_iff_differentials`. -/

/-- Linear independence of the differential family constructs p-independence. -/
@[stacks 07P2 "p-independence from differential independence"]
theorem IsIndependent.of_linearIndependent_differentials {x : ι → K}
    (hx : LinearIndependent K (differentials k x)) : IsIndependent p k x :=
  (isIndependent_iff_differentials p k x).mpr hx
/- Proof strategy: apply the reverse direction of `isIndependent_iff_differentials`. -/

end IndependentAPI

section BasisAPI

variable {p : ℕ} {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K] [Fact p.Prime] [CharP K p]
variable {ι : Type w}

/-- A p-basis has a linearly independent differential family. -/
@[stacks 07P2 "p-basis differential independence"]
theorem IsBasis.linearIndependent_differentials {x : ι → K}
    (hx : IsBasis p k x) : LinearIndependent K (differentials k x) :=
  hx.independent.linearIndependent_differentials
/- Proof strategy: apply `hx.independent.linearIndependent_differentials`.  This proof unit is
independent of the full p-basis characterization below. -/

/-- A p-basis has differentials spanning the whole relative Kähler module. -/
@[stacks 07P2 "p-basis differential spanning"]
theorem IsBasis.span_differentials {x : ι → K} (hx : IsBasis p k x) :
    Submodule.span K (Set.range (differentials k x)) = ⊤ :=
  FieldExtension.Frobenius.Kaehler.span_eq_top_of_adjoin_eq_top p k x hx.adjoin_eq_top
/- Proof strategy: apply the forward direction of
`FieldExtension.Frobenius.Kaehler.adjoin_eq_top_iff_span_eq_top` to `hx.adjoin_eq_top`. -/

/-- Differential independence and spanning construct a p-basis. -/
@[stacks 07P2 "p-basis from a differential basis"]
theorem IsBasis.of_differentials {x : ι → K}
    (hlin : LinearIndependent K (differentials k x))
    (hspan : Submodule.span K (Set.range (differentials k x)) = ⊤) :
    IsBasis p k x :=
  ⟨IsIndependent.of_linearIndependent_differentials hlin,
    FieldExtension.Frobenius.Kaehler.adjoin_eq_top_of_span_eq_top p k x hspan⟩
/- Proof strategy: combine `IsIndependent.of_linearIndependent_differentials hlin` with
`FieldExtension.Frobenius.Kaehler.adjoin_eq_top_of_span_eq_top x hspan` in the defining
conjunction for `IsBasis`. -/

end BasisAPI

section BasisCriterion

variable (p : ℕ) (k : Type u) {K : Type v}
variable [Field k] [Field K] [Algebra k K] [Fact p.Prime] [CharP K p]
variable {ι : Type w}

/-- Lemma 15.46.2, equivalence (a)-(b): a family is a p-basis exactly when its universal
differentials are linearly independent and span the whole Kähler differential module. -/
@[stacks 07P2 "Lemma 15.46.2, equivalence (a)-(b): differential basis criterion"]
theorem isBasis_iff_differentials (x : ι → K) :
    IsBasis p k x ↔
      LinearIndependent K (differentials k x) ∧
        Submodule.span K (Set.range (differentials k x)) = ⊤ := by
  constructor
  · intro hx
    exact ⟨hx.linearIndependent_differentials, hx.span_differentials⟩
  · rintro ⟨hlin, hspan⟩
    exact IsBasis.of_differentials hlin hspan
/- Proof strategy: combine `isIndependent_iff_differentials` with
`FieldExtension.Frobenius.Kaehler.adjoin_eq_top_iff_span_eq_top`. -/

end BasisCriterion

end FieldExtension.PBasis
