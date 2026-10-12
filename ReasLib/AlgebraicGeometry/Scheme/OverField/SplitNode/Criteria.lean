/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.OverField.SplitNode
public import ReasLib.AlgebraicGeometry.Scheme.NodalLocalRing.TrivialQuadraticExtension
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.GenericPoints

@[expose] public section

open AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Hom.PointsOver
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a closed point on a one-dimensional algebraic scheme over a field, being a split node
is equivalent to being a node with exactly two normalization points and trivial residue-field
extensions, and to having completed local ring isomorphic as a base-field algebra to
`MvPowerSeries (Fin 2) k` modulo the `xy` relation. -/
theorem isSplitNode_tfae
    {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X]
    (h_dimension : topologicalKrullDim X.left = 1)
    (x : X.left) (h_closed : x ∈ closedPoints X.left) :
    List.TFAE
      [ isSplitNode X h_dimension x
      , isNode X x ∧
          Function.Bijective (algebraMap k (ResidueField (stalkRing X x))) ∧
          ∃ x₁ x₂ : pointsOver X.left.normalizationTo x,
            x₁ ≠ x₂ ∧
              (∀ y : pointsOver X.left.normalizationTo x, y = x₁ ∨ y = x₂) ∧
                Function.Bijective
                  (residueFieldMap X.left.normalizationTo x x₁).hom ∧
                  Function.Bijective
                    (residueFieldMap X.left.normalizationTo x x₂).hom
      , Nonempty
          (AdicCompletion (maximalIdeal (stalkRing X x)) (stalkRing X x) ≃ₐ[k]
            (MvPowerSeries (Fin 2) k ⧸
              Ideal.span
                {((MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)) :
                  MvPowerSeries (Fin 2) k)}))
      ] := sorry

end AlgebraicGeometry.SchemeOverField
