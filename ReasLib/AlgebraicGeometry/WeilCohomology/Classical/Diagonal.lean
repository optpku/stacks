module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical.Product

@[expose] public section

open CategoryTheory
open scoped BigOperators TensorProduct

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

/-- For a classical Weil cohomology theory, a Künneth decomposition of the
cycle class of the diagonal pairs each basis element with its complementary
degree component by the signed Kronecker delta. -/
theorem integral_basis_mul_diagonalComponent
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle)
    (X : V) (diagonal : X ⟶ product X X)
    (diagonal_fst : diagonal ≫ fst X X = 𝟙 X)
    (diagonal_snd : diagonal ≫ snd X X = 𝟙 X)
    (β : Fin (2 * dimension X + 1) → ℕ)
    (e : ∀ i, Module.Basis (Fin (β i)) F (Hgrade X (i : ℤ)))
    (e' : ∀ i, Fin (β i) → Hgrade X (2 * (dimension X : ℤ) - (i : ℤ)))
    (decomposition : T.cycleClass (product X X)
      (cyclePushforward diagonal (1 : CH X)) =
      T.kunnethMap X X
        (∑ i, ∑ j, (e i j : H X) ⊗ₜ[F] (e' i j : H X))) :
    ∀ (i) (j j' : Fin (β i)),
      T.integral X ((e i j : H X) * (e' i j' : H X)) =
        (-1 : F) ^ (i : ℕ) * if j = j' then 1 else 0 := sorry

end WeilCohomology.ClassicalTheory
