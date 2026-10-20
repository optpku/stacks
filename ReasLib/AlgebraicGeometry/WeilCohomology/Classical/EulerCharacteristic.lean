module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical.Diagonal

@[expose] public section

open CategoryTheory
open scoped BigOperators

universe u v w x y z

namespace WeilCohomology.ClassicalTheory

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {F : Type v} [Field F] [CharZero F]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0}

/-- The Euler characteristic of a smooth projective object in a classical Weil cohomology
theory is the degree of its diagonal self-intersection. -/
theorem eulerChar_eq_diagonalDegree
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle)
    (X : V) (diagonal : X ⟶ product X X)
    (diagonal_fst : diagonal ≫ fst X X = 𝟙 X)
    (diagonal_snd : diagonal ≫ snd X X = 𝟙 X)
    (diagonalCycle : CHgrade (product X X) (dimension X : ℤ))
    (diagonalCycle_eq : (diagonalCycle : CH (product X X)) =
      cyclePushforward diagonal (1 : CH X))
    (diagonalSelfIntersection :
      CHgrade (product X X) (dimension (product X X) : ℤ))
    (diagonalSelfIntersection_eq_square :
      (diagonalSelfIntersection : CH (product X X)) = diagonalCycle * diagonalCycle)
    (toPointProduct : product X X ⟶ point)
    (degreeProduct :
      CHgrade (product X X) (dimension (product X X) : ℤ) →+ ℤ)
    (degreeProduct_spec :
      ∀ alpha : CHgrade (product X X) (dimension (product X X) : ℤ),
        cyclePushforward toPointProduct alpha = degreeProduct alpha • pointCycle) :
    (∑ i : Fin (2 * dimension X + 1),
      (-1 : ℤ) ^ (i : ℕ) * (Module.finrank F (Hgrade X (i : ℤ)) : ℤ)) =
      degreeProduct diagonalSelfIntersection := sorry

/-- The degree of a diagonal self-intersection equals the degree of the top Chern class
of the tangent bundle capped with the fundamental class. -/
theorem diagonalDegree_eq_topChernDegree
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle)
    (X : V) (diagonal : X ⟶ product X X)
    (diagonal_fst : diagonal ≫ fst X X = 𝟙 X)
    (diagonal_snd : diagonal ≫ snd X X = 𝟙 X)
    (diagonalCycle : CHgrade (product X X) (dimension X : ℤ))
    (diagonalCycle_eq : (diagonalCycle : CH (product X X)) =
      cyclePushforward diagonal (1 : CH X))
    (diagonalSelfIntersection :
      CHgrade (product X X) (dimension (product X X) : ℤ))
    (diagonalSelfIntersection_eq_square :
      (diagonalSelfIntersection : CH (product X X)) = diagonalCycle * diagonalCycle)
    (tangentTopChernCap : CHgrade X (dimension X : ℤ))
    (toPointX : X ⟶ point) (toPointProduct : product X X ⟶ point)
    (diagonal_toPoint : diagonal ≫ toPointProduct = toPointX)
    (degreeX : CHgrade X (dimension X : ℤ) →+ ℤ)
    (degreeProduct :
      CHgrade (product X X) (dimension (product X X) : ℤ) →+ ℤ)
    (degreeX_spec : ∀ alpha : CHgrade X (dimension X : ℤ),
      cyclePushforward toPointX alpha = degreeX alpha • pointCycle)
    (degreeProduct_spec :
      ∀ alpha : CHgrade (product X X) (dimension (product X X) : ℤ),
        cyclePushforward toPointProduct alpha = degreeProduct alpha • pointCycle)
    (diagonalSelfIntersection_eq_pushforward_topChern :
      (diagonalSelfIntersection : CH (product X X)) =
        cyclePushforward diagonal tangentTopChernCap) :
    degreeProduct diagonalSelfIntersection = degreeX tangentTopChernCap := sorry

end WeilCohomology.ClassicalTheory
