/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical.Product
import StacksCheckRecall

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

/- Lemma 45.7.5: under the Künneth isomorphism for a classical Weil cohomology
theory, the zero-extended integral on a product is the tensor product of the two
zero-extended integrals. -/
@[stacks 0FGX] #check (WeilCohomology.ClassicalTheory.integral_product :
  ∀ (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
    cyclePullback cyclePushforward pointCycle) (X Y : V),
    T.integral (product X Y) =
      tensorProductTrace (T.kunnethMap X Y) (T.kunnethMap_bijective X Y)
        (T.integral X) (T.integral Y))

/- The product formula evaluated on a pure Künneth tensor. -/
#check (WeilCohomology.ClassicalTheory.integral_kunnethMap_tmul :
  ∀ (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
    cyclePullback cyclePushforward pointCycle) (X Y : V) (a : H X) (b : H Y),
    T.integral (product X Y) (T.kunnethMap X Y (a ⊗ₜ[F] b)) =
      T.integral X a * T.integral Y b)

end WeilCohomology.ClassicalTheory
