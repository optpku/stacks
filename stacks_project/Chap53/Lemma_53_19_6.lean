/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.MvPowerSeries.Nodal

@[expose] public section

noncomputable section

open IsLocalRing
open MvPowerSeries.Jacobian

universe u

/- Lemma 53.19.6 -/
@[stacks 0C4C] #check
  (MvPowerSeries.Jacobian.nodalQuotient_tfae :
    ∀ {k : Type u} [Field k] (n m : ℕ)
      (I : Ideal (MvPowerSeries (Fin n) k))
      (f : Fin m → MvPowerSeries (Fin n) k)
      (hf : Ideal.span (Set.range f) = I)
      (hI : I ≤ maximalIdeal (MvPowerSeries (Fin n) k)),
    let B := MvPowerSeries (Fin n) k ⧸ I
    letI : IsLocalRing B := IsLocalRing.quotient_of_le_maximalIdeal I hI
    let κ := ResidueField B
    let V := CotangentSpace B
    let hasQuadraticRelation :=
      ∃ (e : Module.Basis (Fin 2) κ V) (a b c : κ),
        4 * a * c - b ^ 2 ≠ 0 ∧
          idealConormalAlgebraQuotient (maximalIdeal B)
              (a • SymmetricAlgebra.ι κ V (e 0) ^ 2 +
                b • (SymmetricAlgebra.ι κ V (e 0) * SymmetricAlgebra.ι κ V (e 1)) +
                c • SymmetricAlgebra.ι κ V (e 1) ^ 2) = 0
    let nodalCondition :=
      Algebra.IsSeparableOver k κ ∧ IsReduced B ∧
        Module.finrank κ V = 2 ∧ hasQuadraticRelation
    let jacobianCondition :=
      minorIdeal I (AlgEquiv.refl : MvPowerSeries (Fin n) k ≃ₐ[k]
        MvPowerSeries (Fin n) k) f (n - 1) = maximalIdeal B
    List.TFAE
      [nodalCondition, IsReduced B ∧ jacobianCondition,
        moduleDepth B B = 1 ∧ jacobianCondition])
