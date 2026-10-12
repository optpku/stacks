/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Topology.Adic.Basic

/-!
# Continuity for adic topologies

@stack 07E9
@stack 07EC
-/

@[expose] public section

open scoped Topology

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

section OpenKernel

variable [TopologicalSpace R] [IsTopologicalRing R]
variable [TopologicalSpace S] [IsTopologicalRing S]

/-- A ring homomorphism is continuous when its kernel contains an open ideal. -/
theorem continuous_of_open_ideal_le_ker (φ : R →+* S) (I : Ideal R)
    (hIopen : IsOpen (I : Set R)) (hIker : I ≤ RingHom.ker φ) :
    Continuous φ := sorry

end OpenKernel

section DiscreteTarget

variable [TopologicalSpace R] [IsTopologicalRing R]
variable [TopologicalSpace S] [IsTopologicalRing S] [DiscreteTopology S]

/-- A continuous map from an adic ring to a discrete ring kills a power of the defining ideal. -/
theorem pow_le_ker_of_continuous_to_discrete_quotient
    (I : Ideal R) (hI : IsAdic I) (φ : R →+* S) (hφ : Continuous φ) :
    ∃ n : ℕ, I ^ n ≤ RingHom.ker φ := sorry

end DiscreteTarget

/-- A ring homomorphism is adically continuous from `I` to `J` when some
power of `I` maps into `J`.  This formulation is independent of ambient
topology instances and is the canonical input for completion constructions. -/
@[stacks 07E9 "adic-continuous ring maps"]
def AdicContinuous (φ : R →+* S) (I : Ideal R) (J : Ideal S) : Prop :=
  ∃ n : ℕ, Ideal.map φ (I ^ n) ≤ J

namespace AdicContinuous

/-- Construct adic continuity from an explicit exponent. -/
theorem of (φ : R →+* S) (I : Ideal R) (J : Ideal S) (n : ℕ)
    (h : Ideal.map φ (I ^ n) ≤ J) :
    φ.AdicContinuous I J := sorry

/-- Adic continuity supplies an exponent whose source-ideal power maps into
the target ideal. -/
theorem exists_pow_map_le {φ : R →+* S} {I : Ideal R} {J : Ideal S}
    (h : φ.AdicContinuous I J) :
    ∃ n : ℕ, Ideal.map φ (I ^ n) ≤ J := sorry

/-- Mapping the source ideal into the target ideal implies adic continuity. -/
theorem of_map_le {φ : R →+* S} {I : Ideal R} {J : Ideal S}
    (h : Ideal.map φ I ≤ J) :
    φ.AdicContinuous I J := sorry

/-- Adic continuity is preserved when the source ideal is decreased and the
target ideal is enlarged. -/
theorem mono {φ : R →+* S} {I I' : Ideal R} {J J' : Ideal S}
    (h : φ.AdicContinuous I J) (hI : I' ≤ I) (hJ : J ≤ J') :
    φ.AdicContinuous I' J' := sorry

/-- The identity ring homomorphism is adically continuous for every ideal. -/
theorem id (I : Ideal R) :
    (RingHom.id R).AdicContinuous I I := sorry

/-- A composite of adically continuous ring homomorphisms is adically
continuous. -/
theorem comp {T : Type w} [CommRing T] {φ : R →+* S} {ψ : S →+* T}
    {I : Ideal R} {J : Ideal S} {K : Ideal T}
    (hφ : φ.AdicContinuous I J) (hψ : ψ.AdicContinuous J K) :
    (ψ.comp φ).AdicContinuous I K := sorry

/-- Adic continuity is equivalent to mapping a suitable source power into
every prescribed target power. -/
theorem iff_forall_pow (φ : R →+* S) (I : Ideal R) (J : Ideal S) :
    φ.AdicContinuous I J ↔
      ∀ m : ℕ, ∃ n : ℕ, Ideal.map φ (I ^ n) ≤ J ^ m := sorry

/-- Adic continuity is equivalent to continuity for the corresponding adic
topologies. -/
-- Local instance justification (noncanonical choice): The assertion selects the explicitly supplied I-adic and J-adic topologies, not ambient canonical instances.
theorem iff_continuous (φ : R →+* S) (I : Ideal R) (J : Ideal S) :
    φ.AdicContinuous I J ↔
      (letI : TopologicalSpace R := I.adicTopology
       letI : TopologicalSpace S := J.adicTopology
       Continuous φ) := sorry

/-- Topological continuity between adic topologies gives adic continuity. -/
-- Local instance justification (noncanonical choice): The hypothesis selects the explicitly supplied I-adic and J-adic topologies, not ambient canonical instances.
theorem of_continuous (φ : R →+* S) (I : Ideal R) (J : Ideal S)
    (h : letI : TopologicalSpace R := I.adicTopology
         letI : TopologicalSpace S := J.adicTopology
         Continuous φ) :
    φ.AdicContinuous I J := sorry

/-- An adically continuous map is continuous between the corresponding adic
topologies. -/
-- Local instance justification (noncanonical choice): The conclusion selects the explicitly supplied I-adic and J-adic topologies, not ambient canonical instances.
theorem continuous {φ : R →+* S} {I : Ideal R} {J : Ideal S}
    (h : φ.AdicContinuous I J) :
    letI : TopologicalSpace R := I.adicTopology
    letI : TopologicalSpace S := J.adicTopology
    Continuous φ := sorry

/-- A chosen exponent witnessing adic continuity. -/
@[stacks 07E9 "chosen exponent witnessing adic continuity"]
noncomputable def exponent {φ : R →+* S} {I : Ideal R} {J : Ideal S}
    (h : φ.AdicContinuous I J) : ℕ :=
  Classical.choose h

/-- The chosen adic-continuity exponent maps the corresponding source-ideal
power into the target ideal. -/
theorem exponent_spec {φ : R →+* S} {I : Ideal R} {J : Ideal S}
    (h : φ.AdicContinuous I J) :
    Ideal.map φ (I ^ h.exponent) ≤ J := sorry

/-- Multiples of the chosen exponent map source-ideal powers into the
corresponding target-ideal powers. -/
theorem map_pow_le_pow {φ : R →+* S} {I : Ideal R} {J : Ideal S}
    (h : φ.AdicContinuous I J) (n : ℕ) :
    Ideal.map φ (I ^ (h.exponent * n)) ≤ J ^ n := sorry

/-- A ring homomorphism between the `I`-adic and `J`-adic
topologies is continuous exactly when a positive power of `I` maps into `J`. -/
-- Local instance justification (noncanonical choice): The assertion selects the explicitly supplied I-adic and J-adic topologies, not ambient canonical instances.
@[stacks 07E9]
theorem continuous_iff_exists_pos (φ : R →+* S) (I : Ideal R) (J : Ideal S) :
    (letI : TopologicalSpace R := I.adicTopology
     letI : TopologicalSpace S := J.adicTopology
     Continuous φ) ↔
      ∃ n : ℕ+, Ideal.map φ (I ^ (n : ℕ)) ≤ J := sorry

end AdicContinuous

/-- A ring homomorphism is continuous between two adic topologies exactly
when some source-ideal power maps into the target ideal. -/
-- Local instance justification (noncanonical choice): The assertion selects the explicitly supplied I-adic and J-adic topologies, not ambient canonical instances.
theorem continuous_adic_iff_exists_pow_map_le
    (φ : R →+* S) (I : Ideal R) (J : Ideal S) :
    letI : TopologicalSpace R := I.adicTopology
    letI : TopologicalSpace S := J.adicTopology
    Continuous φ ↔
      ∃ n : ℕ, Ideal.map φ (I ^ n) ≤ J := sorry

end RingHom

namespace Ideal

/-- If `I ≤ J`, then the `I`-adic topology is finer than the `J`-adic topology. -/
theorem adicTopology_mono {I J : Ideal R} (hIJ : I ≤ J) :
    I.adicTopology ≤ J.adicTopology := sorry

end Ideal
