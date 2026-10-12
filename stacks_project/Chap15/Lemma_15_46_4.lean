/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Kaehler.CharP.Subfield.DirectedIntersection
public import ReasLib.FieldTheory.Frobenius.FiniteExtension

/-!
# Lemma 15.46.4

@stack 07P4

The chapter entry is a source-facing check block.  The reusable Kähler and finite-extension
statements live in their mathematical owners, with the chapter notation and proof scaffolding
kept out of the shared layer.
-/

@[expose] public section

universe u v w

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]

/- @stack 07P4 -/
@[stacks 07P4 "Lemma 15.46.4 (1): intersection of differential kernels"]
#check fun {A : Type v} (h_nonempty : Nonempty A) (Kα : A → Subfield K)
    (h_inter : FieldExtension.Frobenius.subfield p K = ⨅ α, Kα α)
    (h_directed : Directed (· ≥ ·) Kα) ↦
  KaehlerDifferential.CharP.SubfieldMap.iInf_ker_eq_bot
    (p := p) (K := K) h_nonempty Kα h_inter h_directed

section FiniteExtension

variable {L : Type w} [Field L] [Algebra K L] [FiniteDimensional K L] [CharP L p]

/- @stack 07P4 -/
@[stacks 07P4 "Lemma 15.46.4 (2): finite-extension Frobenius intersection"]
#check fun {A : Type v} (Kα : A → Subfield K)
    (h_inter : FieldExtension.Frobenius.subfield p K = ⨅ α, Kα α)
    (h_directed : Directed (· ≥ ·) Kα) ↦
  FieldExtension.Frobenius.subfield_eq_iInf_compositum_toSubfield
    (p := p) (K := K) (L := L) Kα h_inter h_directed

end FiniteExtension

#check @KaehlerDifferential.CharP.SubfieldMap.iInf_ker_eq_bot
#check @FieldExtension.Frobenius.compositumMap
#check @FieldExtension.Frobenius.subfield_eq_iInf_compositumMap
#check @FieldExtension.Frobenius.compositum_toSubfield_eq_compositumMap

end
