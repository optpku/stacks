module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.Coproduct
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.Nontriviality
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections.Degree
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology

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

namespace SchemeClassicalTheory

variable (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
  H CH Hgrade CHgrade cyclePullback cyclePushforward)

/-- Multiplication on the bidegree `(0, 0)` part of a classical Weil cohomology
theory is commutative. -/
theorem degreeZero_mul_comm
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    (X : V) (a b : Hgrade X (0, 0)) :
    a * b = b * a := sorry

/-- The canonical commutative-ring structure on the bidegree `(0, 0)` part of a
specified classical Weil cohomology theory. -/
@[reducible]
def degreeZeroCommRing
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    (X : V) : CommRing (Hgrade X (0, 0)) :=
  { (inferInstance : Ring (Hgrade X (0, 0))) with
    mul_comm := T.degreeZero_mul_comm X }

/-- The underlying ring operations of `degreeZeroCommRing` are the canonical
operations on the homogeneous zero piece. -/
theorem degreeZeroCommRing_toRing
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    (X : V) :
    (T.degreeZeroCommRing X).toRing =
      (inferInstance : Ring (Hgrade X (0, 0))) := sorry

/-- The untwisted cohomology of a nonempty equidimensional smooth projective
scheme of dimension zero vanishes outside degree zero. -/
theorem cohomologyEqBotOfDimensionZero
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X : V} (hX : T.IsNonemptyEquidimensional X 0) (i : ℤ) (hi : i ≠ 0) :
    Hgrade X (i, 0) = ⊥ := sorry

/-- Degree-zero cohomology is finite and separable over the coefficient field. -/
theorem degreeZeroFiniteSeparable
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X : V} (hX : T.IsNonemptyEquidimensional X 0) :
    Module.Finite F (Hgrade X (0, 0)) ∧
      @Algebra.IsSeparable F (Hgrade X (0, 0)) inferInstance
        (T.degreeZeroCommRing X).toRing inferInstance := sorry

/-- The coefficient-field dimension of degree-zero cohomology equals the
dimension of the represented scheme's global-sections algebra over `k`. -/
theorem degreeZeroFinrankEqSchemeDegree
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X : V} (hX : T.IsNonemptyEquidimensional X 0) :
    Module.finrank F (Hgrade X (0, 0)) =
      SchemeOverField.GlobalSections.finrank (T.scheme.obj X) := sorry

/-- Integration restricted to degree-zero cohomology is the algebra trace. -/
theorem degreeZeroIntegralEqTrace
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X : V} (hX : T.IsNonemptyEquidimensional X 0) :
    (T.integral hX).comp (Hgrade X (0, 0)).subtype =
      @Algebra.trace F (Hgrade X (0, 0)) inferInstance
        (T.degreeZeroCommRing X) inferInstance := sorry

/-- The degree-zero integration map agrees pointwise with the algebra trace. -/
theorem degreeZeroIntegralApply
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X : V} (hX : T.IsNonemptyEquidimensional X 0)
    (a : Hgrade X (0, 0)) :
    T.integral hX a =
      @Algebra.trace F (Hgrade X (0, 0)) inferInstance
        (T.degreeZeroCommRing X) inferInstance a := sorry

/-- The fundamental cycle class of a nonempty dimension-zero scheme is the
unit in degree-zero cohomology. -/
theorem fundamentalCycleClassEqOneOfDimensionZero
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X : V} (hX : T.IsNonemptyEquidimensional X 0) :
    T.cycleClass X (1 : CHgrade X 0) = 1 := sorry

/-- The integral of the fundamental cycle class equals the degree of the
represented zero-dimensional scheme over `k`. -/
theorem integralFundamentalCycleClassEqSchemeDegree
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X : V} (hX : T.IsNonemptyEquidimensional X 0) :
    T.integral hX (T.cycleClass X (1 : CHgrade X 0)) =
      (SchemeOverField.GlobalSections.finrank (T.scheme.obj X) : F) := sorry

end SchemeClassicalTheory

end WeilCohomology
