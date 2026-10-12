/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.Nodal.Normalization

@[expose] public section

noncomputable section

open IsLocalRing

universe u v w

/- Lemma 53.19.4 (1): the reduced quadratic nodal condition is equivalent to the numerical
conditions on a Nagata local `k`-algebra. -/
@[stacks 0C4A] #check
  (IsLocalRing.nodalLocalAlgebra_iff_invariants :
    ∀ (k : Type u) [Field k]
      (A : Type v) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
      (Ash : Type w) [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash],
    let κ := ResidueField A
    let V := CotangentSpace A
    let hasQuadraticRelation :=
      ∃ (e : Module.Basis (Fin 2) κ V) (a b c : κ),
        4 * a * c - b ^ 2 ≠ 0 ∧
          idealConormalAlgebraQuotient (maximalIdeal A)
              (a • SymmetricAlgebra.ι κ V (e 0) ^ 2 +
                b • (SymmetricAlgebra.ι κ V (e 0) * SymmetricAlgebra.ι κ V (e 1)) +
                c • SymmetricAlgebra.ι κ V (e 1) ^ 2) = 0
    let nodalCondition :=
      Algebra.IsSeparableOver k κ ∧ IsReduced A ∧
        Module.finrank κ V = 2 ∧ hasQuadraticRelation
    let invariantCondition :=
      Algebra.IsSeparableOver k κ ∧ IsReduced A ∧ ringKrullDim A = 1 ∧
        Normalization.deltaInvariant A = 1 ∧ geometricBranchNumber A Ash = 2
    nodalCondition ↔ invariantCondition)

/- Lemma 53.19.4 (2): under the nodal numerical conditions, the normalization has either one
or two maximal ideals. -/
@[stacks 0C4A] #check
  (Normalization.maximalSpectrum_card_of_nodal :
    ∀ (k : Type u) [Field k]
      (A : Type v) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
      (Ash : Type w) [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
      [Algebra.IsSeparableOver k (ResidueField A)] [IsReduced A]
      (h_dimension : ringKrullDim A = 1)
      (h_delta : Normalization.deltaInvariant A = 1)
      (h_branches : geometricBranchNumber A Ash = 2),
    ENat.card (MaximalSpectrum (Normalization.normalizationRing A)) = 1 ∨
      ENat.card (MaximalSpectrum (Normalization.normalizationRing A)) = 2)

/- Lemma 53.19.4 (3): under the nodal numerical conditions, every residue field of the
normalization is separable over the base field through the canonical composite map. -/
@[stacks 0C4A] #check
  (Normalization.residueField_isSeparableOver_of_nodal :
    ∀ (k : Type u) [Field k]
      (A : Type v) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
      (Ash : Type w) [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
      [Algebra.IsSeparableOver k (ResidueField A)] [IsReduced A]
      (h_dimension : ringKrullDim A = 1)
      (h_delta : Normalization.deltaInvariant A = 1)
      (h_branches : geometricBranchNumber A Ash = 2)
      (m : MaximalSpectrum (Normalization.normalizationRing A)),
    Algebra.IsSeparableOver k m.ResidueField)
