/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Definition_87_7_1_WeaklyAdic

/-!
# Taut presentations of linearly topologized rings by pre-adic sources

A taut continuous homomorphism from a pre-adic topological ring is the
presentation used to characterize weakly pre-adic rings. The source topology is
stored as instance fields so a competing `I`-adic topology on the same carrier
need not be registered globally.
-/

@[expose] public section

universe u v

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
  sorry

/-- The bundled source recovers the supplied pre-adic ring. -/
theorem of_source {A' : Type v} [CommRing A'] [TopologicalSpace A'] [IsPreadicRing A']
    [IsLinearTopology A' A'] (φ : A' →+* A) (hcont : Continuous φ) (htaut : φ.IsTaut) :
    (of φ hcont htaut).source = A' :=
  sorry

/-- The smart constructor recovers the supplied source and ring homomorphism. -/
theorem of_spec {A' : Type v} [CommRing A'] [TopologicalSpace A'] [IsPreadicRing A']
    [IsLinearTopology A' A'] (φ : A' →+* A) (hcont : Continuous φ) (htaut : φ.IsTaut) :
    (of φ hcont htaut).source = A' ∧ (of φ hcont htaut).toRingHom = φ :=
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
  continuous :=
    (sorry : @Continuous A A I.adicTopology _ (RingHom.id A))
  isTaut :=
    (sorry : @RingHom.IsTaut A A _ I.adicTopology
      (Ideal.nonarchimedean I).toIsTopologicalRing (Ideal.isLinearTopology I) _ _ _ _
      (RingHom.id A))

/-- The `I`-adic identity presentation has source `A`. -/
theorem ofAdicId_source {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    (ofAdicId hI).source = A :=
  sorry

/-- The `I`-adic identity presentation is the identity ring homomorphism. -/
theorem ofAdicId_toRingHom {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    (ofAdicId hI).toRingHom = RingHom.id A :=
  sorry

/-- The `I`-adic identity presentation uses the `I`-adic topology on the source. -/
theorem ofAdicId_topologicalSpace {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    (ofAdicId hI).topologicalSpace = I.adicTopology :=
  sorry

/-- The identity presentation recovers the carrier, the `I`-adic topology, and
the identity homomorphism. -/
theorem ofAdicId_spec {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    (ofAdicId hI).source = A ∧ (ofAdicId hI).topologicalSpace = I.adicTopology ∧
      (ofAdicId hI).toRingHom = RingHom.id A :=
  sorry

/-- A taut continuous map from a pre-adic ring implies that the target is weakly
pre-adic. -/
theorem isWeaklyPreadicRing (f : TautPreadicHom A) : IsWeaklyPreadicRing A :=
  sorry

end TautPreadicHom

namespace IsWeaklyPreadicRing

variable {A : Type u}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- A linearly topologized ring receiving a taut continuous map from a pre-adic
ring is weakly pre-adic. -/
theorem of_isPreadicRing_isTaut {A' : Type v} [CommRing A'] [TopologicalSpace A']
    [IsPreadicRing A'] [IsLinearTopology A' A'] {φ : A' →+* A} (hcont : Continuous φ)
    (htaut : φ.IsTaut) : IsWeaklyPreadicRing A :=
  sorry

end IsWeaklyPreadicRing

end TopologicalRing
