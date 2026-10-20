module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import ReasLib.RingTheory.LocalRing.Quotient
public import ReasLib.RingTheory.LocalRing.Nodal
public import ReasLib.RingTheory.MvPowerSeries.Jacobian
public import ReasLib.RingTheory.MvPowerSeries.Noetherian

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace MvPowerSeries.Jacobian

/-- For a finite-variable formal power-series quotient, nodality is equivalent to
reducedness or depth one together with the maximal Jacobian-minor condition. -/
theorem nodalQuotient_tfae {k : Type u} [Field k] (n m : ℕ)
    (I : Ideal (MvPowerSeries (Fin n) k))
    (f : Fin m → MvPowerSeries (Fin n) k)
    (hf : Ideal.span (Set.range f) = I)
    (hI : I ≤ maximalIdeal (MvPowerSeries (Fin n) k)) :
    let B := MvPowerSeries (Fin n) k ⧸ I
    -- Local instance justification (defeq pin): pin the canonical quotient local-ring instance determined by hI to keep the dependent residue-field, cotangent-space, and maximal-ideal expressions definitionally aligned.
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
        moduleDepth B B = 1 ∧ jacobianCondition] := sorry

end MvPowerSeries.Jacobian
