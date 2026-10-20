module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical.Degree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

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

/- Lemma 45.7.4: for a classical Weil cohomology theory, the integral of the
cycle class of a top-codimension cycle `α` is the image in `F` of its integer
degree. The degree is characterized by pushforward to the point object. -/
@[stacks 0FGW] #check
  (WeilCohomology.ClassicalTheory.integral_cycleClass_eq_degree :
    ∀ (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
        cyclePullback cyclePushforward pointCycle)
      (X : V) (toPoint : X ⟶ point)
      (degree : CHgrade X (dimension X : ℤ) →+ ℤ),
      (∀ α : CHgrade X (dimension X : ℤ),
        cyclePushforward toPoint α = degree α • pointCycle) →
      ∀ α : CHgrade X (dimension X : ℤ),
        T.integral X (T.cycleClass X α) = (degree α : F))

end WeilCohomology.ClassicalTheory
