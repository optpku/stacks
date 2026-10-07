module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical.Pushforward
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

/- Lemma 45.7.6: pushforward along the second projection sends the Künneth image
of `a ⊗ₜ[F] b` to `(T.integral X a) • b`. -/
@[stacks 0FGY] #check (WeilCohomology.ClassicalTheory.pushforward_snd_kunnethMap_tmul :
  ∀ (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
    cyclePullback cyclePushforward pointCycle) (X Y : V) (a : H X) (b : H Y),
    T.pushforward (snd X Y) (T.kunnethMap X Y (a ⊗ₜ[F] b)) =
      (T.integral X a) • b)

end WeilCohomology.ClassicalTheory
