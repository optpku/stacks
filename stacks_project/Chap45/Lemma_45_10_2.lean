module

public import stacks_project.Chap45.Lemma_45_10_1
public import stacks_project.Chap45.Lemma_45_10_2_DegreeZero
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.DimensionZero
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

/- Lemma 45.10.2: zero-dimensional scheme-classical Weil cohomology conclusions. -/
@[stacks 0FHQ] #check
  (WeilCohomology.SchemeClassicalTheory.cohomologyEqBotOfDimensionZero :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X : V} (hX : T.IsNonemptyEquidimensional X 0) (i : ℤ) (hi : i ≠ 0),
      Hgrade X (i, 0) = ⊥)

/- Lemma 45.10.2 (2): degree-zero cohomology is finite separable. -/
@[stacks 0FHQ] #check
  (WeilCohomology.SchemeClassicalTheory.degreeZeroFiniteSeparable :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X : V} (hX : T.IsNonemptyEquidimensional X 0),
      Module.Finite F (Hgrade X (0, 0)) ∧
        @Algebra.IsSeparable F (Hgrade X (0, 0)) inferInstance
          (T.degreeZeroCommRing X).toRing inferInstance)

/- Lemma 45.10.2 (3): the degree-zero finrank equals scheme degree. -/
@[stacks 0FHQ] #check
  (WeilCohomology.SchemeClassicalTheory.degreeZeroFinrankEqSchemeDegree :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X : V} (hX : T.IsNonemptyEquidimensional X 0),
      Module.finrank F (Hgrade X (0, 0)) =
        SchemeOverField.GlobalSections.finrank (T.scheme.obj X))

/- Lemma 45.10.2 (4): integration equals the algebra trace. -/
@[stacks 0FHQ] #check
  (WeilCohomology.SchemeClassicalTheory.degreeZeroIntegralEqTrace :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X : V} (hX : T.IsNonemptyEquidimensional X 0),
      (T.integral hX).comp (Hgrade X (0, 0)).subtype =
        @Algebra.trace F (Hgrade X (0, 0)) inferInstance
          (T.degreeZeroCommRing X) inferInstance)

/- Pointwise companion for the trace identity. -/
#check
  (WeilCohomology.SchemeClassicalTheory.degreeZeroIntegralApply :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X : V} (hX : T.IsNonemptyEquidimensional X 0)
      (a : Hgrade X (0, 0)),
      T.integral hX a =
        @Algebra.trace F (Hgrade X (0, 0)) inferInstance
          (T.degreeZeroCommRing X) inferInstance a)

/- Lemma 45.10.2 (5): the fundamental cycle class is one. -/
@[stacks 0FHQ] #check
  (WeilCohomology.SchemeClassicalTheory.fundamentalCycleClassEqOneOfDimensionZero :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X : V} (hX : T.IsNonemptyEquidimensional X 0),
      T.cycleClass X (1 : CHgrade X 0) = 1)

/- Lemma 45.10.2 (6): integrating the fundamental class gives scheme degree. -/
@[stacks 0FHQ] #check
  (WeilCohomology.SchemeClassicalTheory.integralFundamentalCycleClassEqSchemeDegree :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X : V} (hX : T.IsNonemptyEquidimensional X 0),
      T.integral hX (T.cycleClass X (1 : CHgrade X 0)) =
        (SchemeOverField.GlobalSections.finrank (T.scheme.obj X) : F))

end WeilCohomology.SchemeClassicalTheory
