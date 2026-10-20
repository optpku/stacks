module

public import Mathlib.RingTheory.Invariant.Profinite
public import ReasLib.RingTheory.Invariant.ResidueField

@[expose] public section

/-!
# Residue fields of profinite invariant extensions

This file extends the finite invariant-extension API to continuous actions of
profinite groups on discrete rings.  The fraction-field layer mirrors the
corresponding Mathlib declarations, while the residue-field layer installs the
canonical structures attached to a lying-over pair.
@stack 0BRK
-/

universe u v w x y

namespace Ideal.IsFractionRing

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]

/-- Fraction fields of quotient rings at a lying-over pair form a normal
extension under a profinite invariant action. -/
@[stacks 0BRK "normal fraction fields for a profinite invariant action"]
theorem normal_of_profinite
    (G : Type w) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B]
    [ContinuousSMul G B] [Algebra.IsInvariant A B G]
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]
    (K : Type x) (L : Type y) [Field K] [Field L] [Algebra K L]
    [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
    [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
    [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
    [IsScalarTower (A ⧸ P) K L] : Normal K L := sorry
-- Proof strategy: first obtain integrality of `B / A` from
-- `Algebra.IsInvariant.isIntegral_of_profinite`. In the proof of `normal_iff`, represent each
-- element of `L` by a quotient from `B ⧸ Q`, choose an open normal subgroup fixing the finitely
-- many coefficients involved, and apply the finite-quotient theorem
-- `Ideal.IsFractionRing.normal` to the corresponding fixed-point subalgebra.

end Ideal.IsFractionRing

namespace IsFractionRing

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]

/-- For a profinite invariant action, the stabilizer action on the fraction
fields of a lying-over quotient pair is surjective. -/
@[stacks 0BRK "surjective fraction-field stabilizer for a profinite action"]
theorem stabilizerHom_surjective_of_profinite
    (G : Type w) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B]
    [ContinuousSMul G B] [Algebra.IsInvariant A B G]
    (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]
    (K : Type x) (L : Type y) [Field K] [Field L]
    [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
    [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
    [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
    [Algebra K L] [IsScalarTower (A ⧸ P) K L] :
    Function.Surjective (IsFractionRing.stabilizerHom G P Q K L) := sorry
-- Proof strategy: adapt Mathlib's cofiltered lifting argument for
-- `Ideal.Quotient.stabilizerHom_surjective_of_profinite`: for every open normal subgroup use the
-- finite invariant theorem `IsFractionRing.stabilizerHom_surjective`, make the finite sets of
-- compatible lifts into a cofiltered system, and recover an element of `G` from a section of that
-- system. Equality of field automorphisms is checked on the fraction-ring generators.

end IsFractionRing

namespace Ideal.ResidueField.Invariant

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]

/-- Residue fields at a lying-over pair form a normal extension under a
profinite invariant action. -/
@[stacks 0BRK "normal residue fields for a profinite invariant action"]
theorem normal_of_profinite
    (G : Type w) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B]
    [ContinuousSMul G B] [Algebra.IsInvariant A B G]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    -- Local instance justification (defeq pin): select the canonical residue algebra in the profinite normality predicate.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    Normal p.ResidueField q.ResidueField := sorry
-- Proof strategy: install `Ideal.ResidueField.LiesOver.quotientAlgebra` and the canonical scalar
-- towers from the lying-over pair, then specialize `Ideal.IsFractionRing.normal_of_profinite` to
-- the fraction fields `p.ResidueField` and `q.ResidueField`.

/-- Under a profinite invariant action, the stabilizer of a prime surjects
onto the automorphism group of the induced residue-field extension. -/
@[stacks 0BRK "surjective residue-field stabilizer for a profinite action"]
theorem stabilizerHom_surjective_of_profinite
    (G : Type w) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B]
    [ContinuousSMul G B] [Algebra.IsInvariant A B G]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    -- Local instance justification (defeq pin): select the canonical residue algebra in the profinite stabilizer action.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    Function.Surjective (stabilizerHom G p q) := sorry
-- Proof strategy: unfold the residue-field `stabilizerHom`, install the same quotient algebra and
-- scalar towers as in `normal_of_profinite`, and apply
-- `IsFractionRing.stabilizerHom_surjective_of_profinite G p q` to the two residue fields.

end Ideal.ResidueField.Invariant
