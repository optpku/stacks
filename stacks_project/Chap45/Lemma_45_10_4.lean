/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.EulerCharacteristic
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology.SchemeClassicalTheory

open AlgebraicGeometry CategoryTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V},
  (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

variable (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
  H CH Hgrade CHgrade cyclePullback cyclePushforward)

/- Lemma 45.10.4: the alternating cohomological dimension sum is the degree of
the diagonal self-intersection and of the top Chern class of the tangent sheaf. -/
@[stacks 0FHS] #check
  (WeilCohomology.SchemeClassicalTheory.eulerChar_eq_diagonalDegree :
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward) →
      {X : V} → {d : ℕ} → (hX : T.IsNonemptyEquidimensional X d) →
      (diagonal : X ⟶ product X X) →
      diagonal ≫ fst X X = 𝟙 X → diagonal ≫ snd X X = 𝟙 X →
      (diagonalCycle : CHgrade (product X X) (d : ℤ)) →
      (diagonalCycle : CH (product X X)) = cyclePushforward diagonal (1 : CHgrade X 0) →
      (diagonalSelfIntersection : CHgrade (product X X) ((d + d : ℕ) : ℤ)) →
      (diagonalSelfIntersection_eq_square :
        (diagonalSelfIntersection : CH (product X X)) = diagonalCycle * diagonalCycle) →
      (chowTopEquivProduct : CHgrade (product X X) ((d + d : ℕ) : ℤ) ≃+
        @ChowGroup (T.scheme.obj (product X X)).left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ (T.scheme.obj (product X X)).hom
            (T.projective (product X X)).isProper.toLocallyOfFiniteType inferInstance)
          ((T.scheme.obj (product X X)).hom.relativeDimensionFunction
            (fun _ : Spec (CommRingCat.of k) ↦ 0))
          (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _
            (T.scheme.obj (product X X)).hom inferInstance
            (T.projective (product X X)).isProper.toLocallyOfFiniteType
            (fun _ : Spec (CommRingCat.of k) ↦ 0) inferInstance) 0) →
      (chowTopEquivProduct_closedPointClass :
        ∀ p : closedPoints (T.scheme.obj (product X X)).left,
        Algebra.IsSeparable k ((T.scheme.obj (product X X)).left.residueField p) →
          chowTopEquivProduct
              (T.closedPointClass (T.product_isNonemptyEquidimensional hX hX) p) =
            @AlgebraicGeometry.chowClass (T.scheme.obj (product X X)).left
              (@LocallyOfFiniteType.isLocallyNoetherian _ _ (T.scheme.obj (product X X)).hom
                (T.projective (product X X)).isProper.toLocallyOfFiniteType inferInstance)
              ((T.scheme.obj (product X X)).hom.relativeDimensionFunction
                (fun _ : Spec (CommRingCat.of k) ↦ 0))
              (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _
                (T.scheme.obj (product X X)).hom inferInstance
                (T.projective (product X X)).isProper.toLocallyOfFiniteType
                (fun _ : Spec (CommRingCat.of k) ↦ 0) inferInstance) 0
              (CycleGroup.point
                ((T.scheme.obj (product X X)).hom.relativeDimensionFunction
                  (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0 p
                (@SchemeOverField.closedPoint_relativeDimensionFunction_eq_zero k _
                  (T.scheme.obj (product X X))
                  (T.projective (product X X)).isProper.toLocallyOfFiniteType p))) →
      (∑ i : Fin (2 * d + 1), (-1 : ℤ) ^ (i : ℕ) *
        (Module.finrank F (Hgrade X ((i : ℤ), 0)) : ℤ)) =
      @ChowGroup.degree k _ (T.scheme.obj (product X X))
        (T.projective (product X X)).isProper
        (chowTopEquivProduct diagonalSelfIntersection))

#check WeilCohomology.SchemeClassicalTheory.diagonalDegree_eq_topChernDegree

end WeilCohomology.SchemeClassicalTheory
