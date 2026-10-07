module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.Nodal.TrivialQuadraticExtension
public import ReasLib.AlgebraicGeometry.Scheme.NodalLocalRing.TrivialQuadraticExtension

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Hom.PointsOver
open scoped AlgebraicGeometry

universe u v w

/- Remark 53.19.9 (Trivial quadratic extension) (1): for a nodal local `k`-algebra, the
quadratic residue-field algebra splits exactly when the quadratic form is `xy`, the local ring
has two branches, its normalization has two maximal ideals, and its completed local ring is the
`k`-algebra `κ[[x, y]]/(xy)`. -/
@[stacks 0CBU] #check
  (NodalLocalRing.trivialQuadraticExtension_tfae :
    ∀ (k : Type u) [Field k]
    (A : Type v) [CommRing A] [IsLocalRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)]
    (Ah : Type w) [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah],
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
      ])

/- Remark 53.19.9 (Trivial quadratic extension) (2): for a locally Noetherian scheme over `k`,
at a nodal point the splitting condition is equivalent to having exactly two normalization
points over that point, each with residue field equal to the residue field at the original point
via the induced residue-field map. -/
@[stacks 0CBU] #check
  (AlgebraicGeometry.SchemeOverField.trivialQuadraticExtension_iff_two_normalization_points :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [IsLocallyNoetherian X.left] (x : X.left)
    [IsNodalLocalRing (stalkRing X x)]
    [Algebra.IsSeparableOver k (ResidueField (stalkRing X x))],
    Nonempty
        (NodalLocalRing.quadraticAlgebra (stalkRing X x) ≃ₐ[ResidueField (stalkRing X x)]
          (ResidueField (stalkRing X x) × ResidueField (stalkRing X x))) ↔
      ∃ x₁ x₂ : pointsOver X.left.normalizationTo x, x₁ ≠ x₂ ∧
        (∀ y : pointsOver X.left.normalizationTo x, y = x₁ ∨ y = x₂) ∧
        Function.Bijective
            (residueFieldMap X.left.normalizationTo x x₁).hom ∧
          Function.Bijective
            (residueFieldMap X.left.normalizationTo x x₂).hom)
