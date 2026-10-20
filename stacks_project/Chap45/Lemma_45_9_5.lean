module

public import stacks_project.Chap45.Lemma_45_9_5_SchemeTheory
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.Nontriviality
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

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

/- Lemma 45.9.5 (1): every class in the total cohomology of an empty smooth
projective scheme is zero. -/
@[stacks 0FHF] #check
  (WeilCohomology.SchemeClassicalTheory.cohomology_eq_zero_of_isEmpty :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward),
      ∀ (X : V), [IsEmpty (T.scheme.obj X).left] → ∀ a : H X, a = 0)

/- Lemma 45.9.5 (2): the cycle class of the fundamental class of a nonempty
smooth projective scheme is `1`. -/
@[stacks 0FHF] #check
  (WeilCohomology.SchemeClassicalTheory.fundamentalCycleClass_eq_one :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward),
      ∀ (X : V), [Nonempty (T.scheme.obj X).left] →
        T.cycleClass X (1 : CHgrade X 0) = 1)

/- Lemma 45.9.5 (3): the unit in degree-zero cohomology of a nonempty smooth
projective scheme is nonzero. -/
@[stacks 0FHF] #check
  (WeilCohomology.SchemeClassicalTheory.degreeZero_one_ne_zero :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward),
      ∀ (X : V), [Nonempty (T.scheme.obj X).left] →
        (1 : Hgrade X (0, 0)) ≠ 0)

end WeilCohomology
