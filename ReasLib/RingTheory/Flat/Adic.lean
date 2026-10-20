module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import ReasLib.RingTheory.Topology.Adic.Prime
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.Adic.Hom

/-!
# Flatness away from ideals of definition

Flatness tests for adic homomorphisms using topologically nilpotent elements
and primes in punctured spectra.
-/

@[expose] public section

universe u

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
  Iff.rfl

namespace IsFlatAwayTopologicallyNilpotent

/-- Evaluate source-nilpotent away-flatness at a topologically nilpotent element
of `A`. -/
theorem apply {φ : A →+* B} (h : φ.IsFlatAwayTopologicallyNilpotent) {f : A}
    (hf : IsTopologicallyNilpotent f) :
    ((algebraMap B (Localization.Away (φ f))).comp φ).Flat :=
  h f hf

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
  Iff.rfl

namespace IsFlatAwayTargetTopologicallyNilpotent

/-- Evaluate target-nilpotent away-flatness at a topologically nilpotent element
of `B`. -/
theorem apply {φ : A →+* B} (h : φ.IsFlatAwayTargetTopologicallyNilpotent) {g : B}
    (hg : IsTopologicallyNilpotent g) :
    ((algebraMap B (Localization.Away g)).comp φ).Flat :=
  h g hg

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
  Iff.rfl

namespace IsFlatAtPrimesAvoidingIdealOfDefinition

/-- Evaluate prime-local flatness at a prime containing no ideal of definition. -/
theorem apply {φ : A →+* B} (h : φ.IsFlatAtPrimesAvoidingIdealOfDefinition)
    {q : Ideal B} [q.IsPrime] (hq : q.ContainsNoIdealOfDefinition) :
    ((algebraMap B (Localization.AtPrime q)).comp φ).Flat :=
  h q hq

end IsFlatAtPrimesAvoidingIdealOfDefinition

/-- `B_q` is flat over `A` at every prime of `B` maximal among primes omitting
some topological ideal of definition. These are closed points of the corresponding
punctured spectrum, extending the rig-closed convention for Noetherian adic rings. -/
def IsFlatAtRigClosed (φ : A →+* B) : Prop :=
  ∀ (q : Ideal B) [q.IsPrime], q.IsMaximalAvoidingIdealOfDefinition →
    ((algebraMap B (Localization.AtPrime q)).comp φ).Flat

/-- Unfold `IsFlatAtRigClosed` as flatness of `A →+* B_q` at primes maximal
among those omitting some topological ideal of definition. -/
theorem isFlatAtRigClosed_iff (φ : A →+* B) :
    φ.IsFlatAtRigClosed ↔
      ∀ (q : Ideal B) [q.IsPrime], q.IsMaximalAvoidingIdealOfDefinition →
        ((algebraMap B (Localization.AtPrime q)).comp φ).Flat :=
  Iff.rfl

namespace IsFlatAtRigClosed

/-- Evaluate prime-local flatness at a prime maximal among those omitting some
topological ideal of definition. -/
theorem apply {φ : A →+* B} (h : φ.IsFlatAtRigClosed) {q : Ideal B} [q.IsPrime]
    (hq : q.IsMaximalAvoidingIdealOfDefinition) :
    ((algebraMap B (Localization.AtPrime q)).comp φ).Flat :=
  h q hq

end IsFlatAtRigClosed

variable [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]

/-- For an adic homomorphism of complete separated adic rings admitting finitely
generated ideals of definition, source-nilpotent away-flatness is equivalent to
target-nilpotent away-flatness. -/
theorem isFlatAwayTopologicallyNilpotent_iff_target (φ : A →+* B) (hφ : φ.IsAdicHom)
    (hA : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hB : ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J) :
    φ.IsFlatAwayTopologicallyNilpotent ↔ φ.IsFlatAwayTargetTopologicallyNilpotent :=
  sorry

/-- For an adic homomorphism of complete separated adic rings admitting finitely
generated ideals of definition, source-nilpotent away-flatness is equivalent to
flatness at primes containing no ideal of definition. -/
theorem isFlatAwayTopologicallyNilpotent_iff_primes (φ : A →+* B) (hφ : φ.IsAdicHom)
    (hA : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hB : ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J) :
    φ.IsFlatAwayTopologicallyNilpotent ↔ φ.IsFlatAtPrimesAvoidingIdealOfDefinition :=
  sorry

/-- For an adic homomorphism of complete separated adic rings admitting finitely
generated ideals of definition, source-nilpotent away-flatness is equivalent to
flatness at primes maximal among those omitting some ideal of definition. -/
theorem isFlatAwayTopologicallyNilpotent_iff_rigClosed (φ : A →+* B) (hφ : φ.IsAdicHom)
    (hA : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hB : ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J) :
    φ.IsFlatAwayTopologicallyNilpotent ↔ φ.IsFlatAtRigClosed :=
  sorry

/-- For an adic homomorphism of complete separated adic rings admitting finitely
generated ideals of definition, flatness after inverting topologically nilpotent
source elements, flatness after inverting topologically nilpotent target elements,
flatness at primes containing no ideal of definition, and flatness at maximal
primes avoiding an ideal of definition are equivalent. -/
theorem isFlatAwayTopologicallyNilpotent_tfae (φ : A →+* B) (hφ : φ.IsAdicHom)
    (hA : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hB : ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J) :
    List.TFAE [φ.IsFlatAwayTopologicallyNilpotent, φ.IsFlatAwayTargetTopologicallyNilpotent,
      φ.IsFlatAtPrimesAvoidingIdealOfDefinition, φ.IsFlatAtRigClosed] :=
  sorry


end RingHom
