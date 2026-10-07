module

public import Mathlib.Data.List.TFAE
public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Lemma_87_5_3_Completion
public import stacks_project.Chap87.Lemma_87_7_2_TautPreadic

/-!
# Lemma 87.7.2

A linearly topologized ring is weakly pre-adic if and only if it receives a taut
continuous map from a pre-adic ring, equivalently if it is pre-admissible and
the closures of positive powers of some (equivalently, every) ideal of
definition are open. The inverse-limit completion of a weakly pre-adic ring is
weakly adic. A weakly adic ring is admissible and has a countable fundamental
system of open ideals.
-/

@[expose] public section

universe u

open scoped Topology
open TopologicalRing IsLinearTopology

variable {A : Type u}
variable [CommRing A] [TopologicalSpace A]

namespace TopologicalRing.Ideal

/-- An ideal of definition whose positive powers have open closures is weakly
adic. -/
theorem IsWeaklyAdic.of_isIdealOfDefinition [IsTopologicalRing A] {I : Ideal A}
    (hI : IsIdealOfDefinition I)
    (hopen : ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A)) : IsWeaklyAdic I :=
  sorry

end TopologicalRing.Ideal

namespace TopologicalRing

/-- A weakly pre-adic ring is pre-admissible. -/
instance instIsPreadmissibleRing_of_isWeaklyPreadicRing [IsWeaklyPreadicRing A] :
    IsPreadmissibleRing A :=
  sorry

namespace IsWeaklyPreadicRing

/-- Lemma 87.7.2 (1): Let `A` be a linearly topologized ring. The following are
equivalent: `A` is weakly pre-adic; there exists a taut continuous ring map
`A' →+* A` with `A'` pre-adic; `A` is pre-admissible and some ideal of definition
`I` has `(I ^ n).closure` open for all `n ≥ 1`; and the same holds for every
ideal of definition. -/
@[stacks 0GXF]
theorem tfae [IsTopologicalRing A] [IsLinearTopology A A] :
    List.TFAE
      [ IsWeaklyPreadicRing A
      , Nonempty (TautPreadicHom.{u, u} A)
      , IsPreadmissibleRing A ∧
          ∃ I : Ideal A, Ideal.IsIdealOfDefinition I ∧
            ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A)
      , IsPreadmissibleRing A ∧
          ∀ I : Ideal A, Ideal.IsIdealOfDefinition I →
            ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A) ] :=
  sorry

/-- A linearly topologized ring is weakly pre-adic if and only if it admits a taut
pre-adic presentation. -/
theorem iff_nonempty_tautPreadicHom [IsTopologicalRing A] [IsLinearTopology A A] :
    IsWeaklyPreadicRing A ↔ Nonempty (TautPreadicHom.{u, u} A) :=
  sorry

/-- A linearly topologized ring is weakly pre-adic if and only if it is
pre-admissible and some ideal of definition has open closures of positive
powers. -/
theorem iff_exists_isIdealOfDefinition [IsTopologicalRing A] [IsLinearTopology A A] :
    IsWeaklyPreadicRing A ↔
      IsPreadmissibleRing A ∧
        ∃ I : Ideal A, Ideal.IsIdealOfDefinition I ∧
          ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A) :=
  sorry

/-- A linearly topologized ring is weakly pre-adic if and only if it is
pre-admissible and every ideal of definition has open closures of positive
powers. -/
theorem iff_forall_isIdealOfDefinition [IsTopologicalRing A] [IsLinearTopology A A] :
    IsWeaklyPreadicRing A ↔
      IsPreadmissibleRing A ∧
        ∀ I : Ideal A, Ideal.IsIdealOfDefinition I →
          ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A) :=
  sorry

end IsWeaklyPreadicRing

namespace IsWeaklyAdicRing

/-- Lemma 87.7.2 (2): the inverse-limit completion of a weakly pre-adic ring is
weakly adic. -/
@[stacks 0GXF]
instance instCompletion [IsWeaklyPreadicRing A] :
    IsWeaklyAdicRing (Completion A A) :=
  sorry

end IsWeaklyAdicRing

/-- Lemma 87.7.2 (3): a weakly adic ring is admissible. -/
@[stacks 0GXF]
instance instIsAdmissibleRing_of_isWeaklyAdicRing [IsWeaklyAdicRing A] :
    IsAdmissibleRing A :=
  sorry

/-- Lemma 87.7.2 (4): a weakly adic ring has a countable fundamental system of
open ideals. -/
@[stacks 0GXF]
instance instIsCountablyGenerated_nhds_of_isWeaklyAdicRing [IsWeaklyAdicRing A] :
    (nhds (0 : A)).IsCountablyGenerated :=
  sorry

end TopologicalRing
