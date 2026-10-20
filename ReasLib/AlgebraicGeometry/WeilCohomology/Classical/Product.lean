module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical.Degree
public import ReasLib.AlgebraicGeometry.WeilCohomology.Trace

@[expose] public section

open CategoryTheory
open scoped TensorProduct

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

/-- For a classical Weil cohomology theory, integration on a product is the
tensor-product trace transported through the Künneth isomorphism. -/
theorem integral_product
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle)
    (X Y : V) :
    T.integral (product X Y) =
      tensorProductTrace (T.kunnethMap X Y) (T.kunnethMap_bijective X Y)
        (T.integral X) (T.integral Y) := sorry

/-- Evaluating product integration on a pure Künneth tensor gives the product
of the two factor integrals. -/
theorem integral_kunnethMap_tmul
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle)
    (X Y : V) (a : H X) (b : H Y) :
    T.integral (product X Y) (T.kunnethMap X Y (a ⊗ₜ[F] b)) =
      T.integral X a * T.integral Y b := sorry

end WeilCohomology.ClassicalTheory
