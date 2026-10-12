/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.Lemma_88_14_1_RigClosed

/-!
# Flatness after inverting topologically nilpotent elements

Predicates testing whether an adic homomorphism remains flat after localizing
the target away from topologically nilpotent elements, at primes containing no
ideal of definition, and at rig-closed primes.
-/

@[expose] public section

universe u

namespace Ideal

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- An ideal contains no topological ideal of definition of the ambient ring. -/
def ContainsNoIdealOfDefinition (q : Ideal A) : Prop :=
  ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q

/-- Unfold `ContainsNoIdealOfDefinition` as the absence of a contained ideal of
definition. -/
theorem containsNoIdealOfDefinition_iff (q : Ideal A) :
    q.ContainsNoIdealOfDefinition ↔
      ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q :=
  sorry

namespace ContainsNoIdealOfDefinition

/-- A contained topological ideal of definition is forbidden. -/
theorem apply {q : Ideal A} (hq : q.ContainsNoIdealOfDefinition) {I : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) : ¬ I ≤ q :=
  sorry

end ContainsNoIdealOfDefinition

/-- A prime is maximal among primes omitting some topological ideal of
definition, in the sense of lemma-rig-point (1). This is not the Noetherian
owner `PrimeSpectrum.IsRigClosed` of Definition 88.14.2. -/
def IsMaximalAvoidingIdealOfDefinition (q : Ideal A) : Prop :=
  q.IsPrime ∧
    ∃ I : Ideal A,
      TopologicalRing.Ideal.IsIdealOfDefinition I ∧ ¬ I ≤ q ∧
        ∀ r : Ideal A, r.IsPrime → ¬ I ≤ r → q ≤ r → r = q

/-- Unfold `IsMaximalAvoidingIdealOfDefinition` as primeness together with
maximality among primes omitting some topological ideal of definition. -/
theorem isMaximalAvoidingIdealOfDefinition_iff (q : Ideal A) :
    q.IsMaximalAvoidingIdealOfDefinition ↔
      q.IsPrime ∧
        ∃ I : Ideal A,
          TopologicalRing.Ideal.IsIdealOfDefinition I ∧ ¬ I ≤ q ∧
            ∀ r : Ideal A, r.IsPrime → ¬ I ≤ r → q ≤ r → r = q :=
  sorry

namespace IsMaximalAvoidingIdealOfDefinition

/-- Such an ideal is prime. -/
theorem isPrime {q : Ideal A} (hq : q.IsMaximalAvoidingIdealOfDefinition) :
    q.IsPrime :=
  sorry

/-- There is a topological ideal of definition omitted by `q`, and `q` is
maximal among primes with that property. -/
theorem exists_idealOfDefinition {q : Ideal A}
    (hq : q.IsMaximalAvoidingIdealOfDefinition) :
    ∃ I : Ideal A,
      TopologicalRing.Ideal.IsIdealOfDefinition I ∧ ¬ I ≤ q ∧
        ∀ r : Ideal A, r.IsPrime → ¬ I ≤ r → q ≤ r → r = q :=
  sorry

end IsMaximalAvoidingIdealOfDefinition

end Ideal

namespace PrimeSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- On a Noetherian adic ring, `PrimeSpectrum.IsRigClosed` is equivalent to
maximality among primes omitting some topological ideal of definition
(lemma-rig-point (1)). -/
theorem IsRigClosed.iff_isMaximalAvoidingIdealOfDefinition (q : PrimeSpectrum A) :
    IsRigClosed q ↔ q.asIdeal.IsMaximalAvoidingIdealOfDefinition :=
  sorry

end PrimeSpectrum

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]
variable [TopologicalSpace A] [TopologicalSpace B]

/-- `B_f` is flat over `A` for every topologically nilpotent `f` in `A`. -/
def IsFlatAwayTopologicallyNilpotent (φ : A →+* B) : Prop :=
  ∀ f : A, IsTopologicallyNilpotent f →
    ((algebraMap B (Localization.Away (φ f))).comp φ).Flat

/-- Unfold `IsFlatAwayTopologicallyNilpotent` as flatness of `A →+* B_f` for
topologically nilpotent `f` in `A`. -/
theorem isFlatAwayTopologicallyNilpotent_iff (φ : A →+* B) :
    φ.IsFlatAwayTopologicallyNilpotent ↔
      ∀ f : A, IsTopologicallyNilpotent f →
        ((algebraMap B (Localization.Away (φ f))).comp φ).Flat :=
  sorry

namespace IsFlatAwayTopologicallyNilpotent

/-- Evaluate source-nilpotent away-flatness at a topologically nilpotent element
of `A`. -/
theorem apply {φ : A →+* B} (h : φ.IsFlatAwayTopologicallyNilpotent) {f : A}
    (hf : IsTopologicallyNilpotent f) :
    ((algebraMap B (Localization.Away (φ f))).comp φ).Flat :=
  sorry

end IsFlatAwayTopologicallyNilpotent

/-- `B_g` is flat over `A` for every topologically nilpotent `g` in `B`. -/
def IsFlatAwayTargetTopologicallyNilpotent (φ : A →+* B) : Prop :=
  ∀ g : B, IsTopologicallyNilpotent g →
    ((algebraMap B (Localization.Away g)).comp φ).Flat

/-- Unfold `IsFlatAwayTargetTopologicallyNilpotent` as flatness of `A →+* B_g`
for topologically nilpotent `g` in `B`. -/
theorem isFlatAwayTargetTopologicallyNilpotent_iff (φ : A →+* B) :
    φ.IsFlatAwayTargetTopologicallyNilpotent ↔
      ∀ g : B, IsTopologicallyNilpotent g →
        ((algebraMap B (Localization.Away g)).comp φ).Flat :=
  sorry

namespace IsFlatAwayTargetTopologicallyNilpotent

/-- Evaluate target-nilpotent away-flatness at a topologically nilpotent element
of `B`. -/
theorem apply {φ : A →+* B} (h : φ.IsFlatAwayTargetTopologicallyNilpotent) {g : B}
    (hg : IsTopologicallyNilpotent g) :
    ((algebraMap B (Localization.Away g)).comp φ).Flat :=
  sorry

end IsFlatAwayTargetTopologicallyNilpotent

/-- `B_q` is flat over `A` at every prime of `B` containing no topological ideal
of definition. -/
def IsFlatAtPrimesAvoidingIdealOfDefinition (φ : A →+* B) : Prop :=
  ∀ (q : Ideal B) [q.IsPrime], q.ContainsNoIdealOfDefinition →
    ((algebraMap B (Localization.AtPrime q)).comp φ).Flat

/-- Unfold `IsFlatAtPrimesAvoidingIdealOfDefinition` as flatness of `A →+* B_q`
at primes containing no ideal of definition. -/
theorem isFlatAtPrimesAvoidingIdealOfDefinition_iff (φ : A →+* B) :
    φ.IsFlatAtPrimesAvoidingIdealOfDefinition ↔
      ∀ (q : Ideal B) [q.IsPrime], q.ContainsNoIdealOfDefinition →
        ((algebraMap B (Localization.AtPrime q)).comp φ).Flat :=
  sorry

namespace IsFlatAtPrimesAvoidingIdealOfDefinition

/-- Evaluate prime-local flatness at a prime containing no ideal of definition. -/
theorem apply {φ : A →+* B} (h : φ.IsFlatAtPrimesAvoidingIdealOfDefinition)
    {q : Ideal B} [q.IsPrime] (hq : q.ContainsNoIdealOfDefinition) :
    ((algebraMap B (Localization.AtPrime q)).comp φ).Flat :=
  sorry

end IsFlatAtPrimesAvoidingIdealOfDefinition

/-- `B_q` is flat over `A` at every prime of `B` that is maximal among primes
omitting some topological ideal of definition (lemma-rig-point (1)). -/
def IsFlatAtRigClosed (φ : A →+* B) : Prop :=
  ∀ (q : Ideal B) [q.IsPrime], q.IsMaximalAvoidingIdealOfDefinition →
    ((algebraMap B (Localization.AtPrime q)).comp φ).Flat

/-- Unfold `IsFlatAtRigClosed` as flatness of `A →+* B_q` at primes maximal
among those omitting some topological ideal of definition. -/
theorem isFlatAtRigClosed_iff (φ : A →+* B) :
    φ.IsFlatAtRigClosed ↔
      ∀ (q : Ideal B) [q.IsPrime], q.IsMaximalAvoidingIdealOfDefinition →
        ((algebraMap B (Localization.AtPrime q)).comp φ).Flat :=
  sorry

namespace IsFlatAtRigClosed

/-- Evaluate prime-local flatness at a prime maximal among those omitting some
topological ideal of definition. -/
theorem apply {φ : A →+* B} (h : φ.IsFlatAtRigClosed) {q : Ideal B} [q.IsPrime]
    (hq : q.IsMaximalAvoidingIdealOfDefinition) :
    ((algebraMap B (Localization.AtPrime q)).comp φ).Flat :=
  sorry

end IsFlatAtRigClosed

variable [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]

/-- For an adic homomorphism of objects of `WAdm^{adic*}`, source-nilpotent
away-flatness is equivalent to target-nilpotent away-flatness. -/
theorem isFlatAwayTopologicallyNilpotent_iff_target (φ : A →+* B) (hφ : φ.IsAdicHom)
    (hA : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hB : ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J) :
    φ.IsFlatAwayTopologicallyNilpotent ↔ φ.IsFlatAwayTargetTopologicallyNilpotent :=
  sorry

/-- For an adic homomorphism of objects of `WAdm^{adic*}`, source-nilpotent
away-flatness is equivalent to flatness at primes containing no ideal of
definition. -/
theorem isFlatAwayTopologicallyNilpotent_iff_primes (φ : A →+* B) (hφ : φ.IsAdicHom)
    (hA : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hB : ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J) :
    φ.IsFlatAwayTopologicallyNilpotent ↔ φ.IsFlatAtPrimesAvoidingIdealOfDefinition :=
  sorry

/-- For an adic homomorphism of objects of `WAdm^{adic*}`, source-nilpotent
away-flatness is equivalent to flatness at primes maximal among those omitting
some topological ideal of definition (lemma-rig-point (1)). -/
theorem isFlatAwayTopologicallyNilpotent_iff_rigClosed (φ : A →+* B) (hφ : φ.IsAdicHom)
    (hA : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hB : ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J) :
    φ.IsFlatAwayTopologicallyNilpotent ↔ φ.IsFlatAtRigClosed :=
  sorry

end RingHom
