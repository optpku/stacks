module

public import Mathlib.Data.List.TFAE
public import Mathlib.Order.Filter.CountablyGenerated
public import ReasLib.RingTheory.Topology.Adic.Weakly.Taut

/-!
# Taut pre-adic presentations and weak pre-adicity

Weak pre-adicity is characterized by taut pre-adic presentations and by open
closures of powers of ideals of definition.
-/

@[expose] public section

universe u v

open scoped Topology
open TopologicalRing

namespace TopologicalRing

/-- A taut continuous homomorphism to `A` from some pre-adic linearly topologized
ring. -/
structure TautPreadicHom (A : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] where
  /-- Source pre-adic topological ring. -/
  source : Type v
  /-- Commutative ring structure on the source. -/
  [commRing : CommRing source]
  /-- Topology on the source, possibly distinct from any ambient topology on the
  same carrier. -/
  [topologicalSpace : TopologicalSpace source]
  /-- The source is a topological ring. -/
  [isTopologicalRing : IsTopologicalRing source]
  /-- The source is linearly topologized. -/
  [isLinearTopology : IsLinearTopology source source]
  /-- The source is pre-adic. -/
  [isPreadicRing : IsPreadicRing source]
  /-- Underlying ring homomorphism. -/
  toRingHom : source →+* A
  /-- The homomorphism is continuous. -/
  continuous : Continuous toRingHom
  /-- The homomorphism is taut. -/
  isTaut : toRingHom.IsTaut

namespace TautPreadicHom

variable {A : Type u}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- Bundle a taut continuous homomorphism from a pre-adic linearly topologized
ring. -/
def of {A' : Type v} [CommRing A'] [TopologicalSpace A'] [IsPreadicRing A']
    [IsLinearTopology A' A'] (φ : A' →+* A) (hcont : Continuous φ) (htaut : φ.IsTaut) :
    TautPreadicHom A where
  source := A'
  toRingHom := φ
  continuous := hcont
  isTaut := htaut

/-- The bundled homomorphism recovers the supplied ring homomorphism. -/
theorem of_toRingHom {A' : Type v} [CommRing A'] [TopologicalSpace A'] [IsPreadicRing A']
    [IsLinearTopology A' A'] (φ : A' →+* A) (hcont : Continuous φ) (htaut : φ.IsTaut) :
    (of φ hcont htaut).toRingHom = φ :=
  rfl

/-- The bundled source recovers the supplied pre-adic ring. -/
theorem of_source {A' : Type v} [CommRing A'] [TopologicalSpace A'] [IsPreadicRing A']
    [IsLinearTopology A' A'] (φ : A' →+* A) (hcont : Continuous φ) (htaut : φ.IsTaut) :
    (of φ hcont htaut).source = A' :=
  rfl

/-- The identity from the adic topology of a weakly adic ideal to the ambient
ring topology is continuous. -/
theorem continuous_adicId {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    @Continuous A A I.adicTopology _ (RingHom.id A) :=
  sorry

/-- The identity from the adic topology of a weakly adic ideal to the ambient
linearly topologized ring is taut. -/
theorem isTaut_adicId {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    @RingHom.IsTaut A A _ I.adicTopology
      (Ideal.nonarchimedean I).toIsTopologicalRing (Ideal.isLinearTopology I) _ _ _ _
      (RingHom.id A) :=
  sorry

/-- The identity on `A`, viewed from the `I`-adic topology, as a taut pre-adic
presentation when `I` is weakly adic. -/
def ofAdicId {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) : TautPreadicHom A where
  source := A
  topologicalSpace := I.adicTopology
  isTopologicalRing := (Ideal.nonarchimedean I).toIsTopologicalRing
  isLinearTopology := Ideal.isLinearTopology I
  isPreadicRing :=
    @IsPreadicRing.mk A _ I.adicTopology (Ideal.nonarchimedean I).toIsTopologicalRing ⟨I, rfl⟩
  toRingHom := RingHom.id A
  continuous := continuous_adicId hI
  isTaut := isTaut_adicId hI

/-- The `I`-adic identity presentation has source `A`. -/
theorem ofAdicId_source {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    (ofAdicId hI).source = A :=
  rfl

/-- The `I`-adic identity presentation is the identity ring homomorphism. -/
theorem ofAdicId_toRingHom {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    (ofAdicId hI).toRingHom = RingHom.id A :=
  rfl

/-- The `I`-adic identity presentation uses the `I`-adic topology on the source. -/
theorem ofAdicId_topologicalSpace {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    (ofAdicId hI).topologicalSpace = I.adicTopology :=
  rfl

/-- A taut continuous map from a pre-adic ring implies that the target is weakly
pre-adic. -/
theorem isWeaklyPreadicRing (f : TautPreadicHom A) : IsWeaklyPreadicRing A := by
  cases f with
  | mk source toRingHom continuous isTaut =>
    exact IsWeaklyPreadicRing.of_isTaut continuous isTaut

end TautPreadicHom

end TopologicalRing

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

/-- A linearly topologized ring is weakly pre-adic if and only if it admits a
taut continuous pre-adic presentation, equivalently if it is pre-admissible
and the closures of positive powers of some, or every, ideal of definition
are open. -/
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

/-- A weakly adic ring is admissible. -/
instance instIsAdmissibleRing_of_isWeaklyAdicRing [IsWeaklyAdicRing A] :
    IsAdmissibleRing A :=
  sorry

/-- A weakly adic ring has a countable fundamental system of open ideals. -/
instance instIsCountablyGenerated_nhds_of_isWeaklyAdicRing [IsWeaklyAdicRing A] :
    (nhds (0 : A)).IsCountablyGenerated :=
  sorry

end TopologicalRing
