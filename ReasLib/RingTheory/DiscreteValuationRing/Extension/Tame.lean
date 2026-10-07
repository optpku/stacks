module

public import ReasLib.FieldTheory.Normal.Closure
public import ReasLib.FieldTheory.Galois.IntegralClosure.Tower
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open Ideal IsLocalRing Algebra

/-!
# Closure properties of tame DVR field extensions

This leaf owns the finite Galois overfield and common-overfield statements for
`DVR.Field.IsTamelyRamified`.  The source-facing Chapter 15 entry is a recall of these
field-model statements; no normal-closure witness is hidden behind a public `Nonempty` datum.

@stack 0EXU
@stack 0EXV
@stack 0EXX
-/

universe u v w x

namespace DVR.Field.IsTamelyRamified

section Tower

variable {A : Type u} {K : Type v} {L : Type w} {M : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra K M] [Algebra L M]
variable [IsScalarTower A K M] [IsScalarTower K L M]
variable [FiniteDimensional K L] [FiniteDimensional L M]
variable [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]

/-- Lemma 15.115.6 (tag `0EXV`): tameness descends to an
intermediate field in a finite separable tower. -/
@[stacks 0EXV "tame ramification descends in a finite separable tower"]
theorem ofTower (hM : IsTamelyRamified A K M) :
    IsTamelyRamified A K L := sorry
-- Proof strategy: for a maximal branch of `integralClosure A L`, choose a maximal branch of
-- `integralClosure A M` above it.  Specialize `hM` at the top branch.  Residue-field separability
-- descends to the intermediate residue field, while multiplicativity of branch ramification
-- indices shows that the intermediate index divides the top index; hence it remains prime to the
-- residue characteristic.  Repackage these two branchwise facts as `IsTamelyRamified A K L`.

end Tower

section IntegralClosureTower

variable {A : Type u} {K : Type v} {L : Type w} {M : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra K M] [Algebra L M]
variable [IsScalarTower A L M] [IsScalarTower A K M] [IsScalarTower K L M]
variable [FiniteDimensional K L] [FiniteDimensional L M]
variable [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A M

/-- Lemma 15.115.5 (tag `0EXU`): the branchwise local
hypothesis for the tame extension `M/L`.  The first conjunct records residue separability on
each upper branch; the second records prime-to-residue-characteristic ramification indices. -/
@[stacks 0EXU "branchwise tame hypothesis in an integral-closure tower"]
def IsTamelyRamifiedOnTower : Prop :=
  (∀ (P : Ideal C) [P.IsMaximal],
      integralClosure.Tower.branchResidueSeparable (A := A) (L := L) (M := M) P) ∧
    (∀ (P : Ideal C) [P.IsMaximal] (q : ℕ) [Fact q.Prime]
      [CharP (integralClosure.Tower.under (A := A) (L := L) (M := M) P).ResidueField q],
      Nat.Coprime
        (integralClosure.Tower.branchRamificationIdx (A := A) (L := L) (M := M) P) q)

/-- Lemma 15.115.5 (tag `0EXU`): tame ramification composes in
an integral-closure tower. -/
@[stacks 0EXU "tame ramification composes in an integral-closure tower"]
theorem ofTameOnIntegralClosureTower
    (hL : IsTamelyRamified A K L)
    (hM : IsTamelyRamifiedOnTower (A := A) (L := L) (M := M)) :
    IsTamelyRamified A K M := sorry
-- Proof strategy: fix a maximal branch `P` of `C` and let its contraction to `B` be the canonical
-- `integralClosure.Tower.under P`.  Specialize `hL` at that lower branch and `hM` at `P`.
-- Compose the two residue-field separability statements through the tower.  Rewrite the top
-- ramification index using `integralClosure.Tower.branchRamificationIdx_eq` and multiplicativity;
-- `Nat.Coprime.mul` combines the two prime-to-characteristic conditions.  Apply the branchwise
-- characterization of `DVR.Field.IsTamelyRamified`.

end IntegralClosureTower

section NormalClosure

variable {A : Type u} {K : Type v} {L : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- Lemma 15.115.8 (tag `0EXX`): the canonical normal closure
inside `AlgebraicClosure L` remains tamely ramified over the base DVR. -/
@[stacks 0EXX "tame ramification of the canonical normal closure"]
theorem normalClosure (hL : IsTamelyRamified A K L) :
    IsTamelyRamified A K (IntermediateField.normalClosure K L (AlgebraicClosure L)) := sorry
-- Proof strategy: express the finite normal closure as the compositum of the finitely many
-- conjugate copies of `L` in `AlgebraicClosure L`.  Transport tameness along each `K`-embedding,
-- then induct over the finite compositum using the integral-closure tower composition theorem:
-- residue separability is stable under compositum and ramification indices remain products of
-- integers prime to the residue characteristic.

/-- Lemma 15.115.8 (tag `0EXX`), clause (1): a finite separable
tame extension is contained in a finite Galois extension that is still tame over the base DVR. -/
@[stacks 0EXX "finite Galois tame overfield"]
theorem existsGaloisExtension (hL : IsTamelyRamified A K L) :
    ∃ (M : Type w) (_ : Field M) (_ : Algebra A M) (_ : Algebra K M) (_ : Algebra L M)
      (_ : IsScalarTower A K M),
      IsScalarTower K L M ∧ FiniteDimensional K M ∧ IsGalois K M ∧
        IsTamelyRamified A K M := sorry
-- Proof strategy: take `M` to be
-- `IntermediateField.normalClosure K L (AlgebraicClosure L)`.  Use its canonical field, `A`-,
-- `K`-, and `L`-algebra structures and scalar towers, together with
-- `normalClosure.is_finiteDimensional`, the canonical `IsGalois` instance, and `normalClosure hL`.

end NormalClosure

section CommonExtension

variable {A : Type u} {K : Type v} {L₁ : Type w} {L₂ : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L₁] [Algebra A L₁] [Algebra K L₁] [IsScalarTower A K L₁]
variable [Field L₂] [Algebra A L₂] [Algebra K L₂] [IsScalarTower A K L₂]
variable [FiniteDimensional K L₁] [FiniteDimensional K L₂]
variable [Algebra.IsSeparable K L₁] [Algebra.IsSeparable K L₂]

/-- Lemma 15.115.8 (tag `0EXX`), clause (2): two finite
separable tame extensions embed in a common finite separable tame extension. -/
@[stacks 0EXX "common finite separable tame overfield"]
theorem existsCommonExtension
    (hL₁ : IsTamelyRamified A K L₁) (hL₂ : IsTamelyRamified A K L₂) :
    ∃ (L : Type (max w x)) (_ : Field L) (_ : Algebra A L) (_ : Algebra K L)
      (_ : Algebra L₁ L) (_ : Algebra L₂ L) (_ : IsScalarTower A K L),
      IsScalarTower K L₁ L ∧ IsScalarTower K L₂ L ∧ FiniteDimensional K L ∧
        Algebra.IsSeparable K L ∧ IsTamelyRamified A K L := sorry
-- Proof strategy: embed `L₁` and `L₂` into finite Galois tame overfields from
-- `existsGaloisExtension`, place both in a common algebraic closure, and take their finite
-- compositum (using the universe-polymorphic common-overfield construction).  Assemble the induced
-- algebra and scalar-tower structures; separability and finite dimensionality are stable under
-- compositum, and the same branchwise tower argument as `normalClosure` proves tameness.

end CommonExtension

end DVR.Field.IsTamelyRamified
