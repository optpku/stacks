/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.Nodal
public import ReasLib.RingTheory.LocalRing.Nodal.Normalization

@[expose] public section

noncomputable section

open IsLocalRing Polynomial

universe u v w

namespace NodalLocalRing

/-- For a nodal local algebra with separable residue field, splitting of the quadratic
residue-field algebra is equivalent to an `xy` cotangent relation, two branches, two maximal
ideals in the normalization, and a completed local algebra of the form `κ[[x, y]]/(xy)`. -/
theorem trivialQuadraticExtension_tfae
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [IsLocalRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)]
    (Ah : Type w) [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah] :
    List.TFAE
      [ Nonempty
          (NodalLocalRing.quadraticAlgebra A ≃ₐ[ResidueField A]
            (ResidueField A × ResidueField A))
      , ∃ (e : Module.Basis (Fin 2) (ResidueField A) (CotangentSpace A)),
          idealConormalAlgebraQuotient (maximalIdeal A)
            (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) = 0
      , branchNumber A Ah = 2
      , ENat.card (MaximalSpectrum (Normalization.normalizationRing A)) = 2
      , Nonempty
          (AdicCompletion (maximalIdeal A) A ≃ₐ[k]
            (MvPowerSeries (Fin 2) (ResidueField A) ⧸
              Ideal.span
                {((MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)) :
                  MvPowerSeries (Fin 2) (ResidueField A))}))
      ] := sorry

end NodalLocalRing
