/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap50.Example_50_19_4_AdjoinRoot
public import stacks_project.Chap50.Example_50_19_4_AffineTrace

@[expose] public section

open AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme
open scoped Polynomial

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace RelativeDifferentials
namespace TraceRule
namespace Affine

/-- Example 50.19.4 (1): for a monic polynomial `p` of positive degree, the absolute de Rham
trace of `dt` is `-da₁`, where `a₁` is the coefficient of degree `d - 1`. -/
@[stacks 0FLD]
theorem dRoot (r : TraceRule.{u}) (hr : IsTraceRule r) {A : Type u} [CommRing A]
    {d : ℕ} (p : Polynomial.MonicDegreeEq A d) (hd : 0 < d) :
    oneForm r hr (AdjoinRoot.of p.1) 1 (AdjoinRoot.root p.1) =
      -AbsoluteDeRham.basicOneForm A 1 (p.1.coeff (d - 1)) := sorry

/-- Example 50.19.4 (2): in degree at least two, the absolute de Rham trace of `t dt` is
`a₁ da₁ - da₂`. -/
@[stacks 0FLD]
theorem rootMulDRoot (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A : Type u} [CommRing A] {d : ℕ} (p : Polynomial.MonicDegreeEq A d) (hd : 1 < d) :
    oneForm r hr (AdjoinRoot.of p.1) (AdjoinRoot.root p.1) (AdjoinRoot.root p.1) =
      AbsoluteDeRham.basicOneForm A (p.1.coeff (d - 1)) (p.1.coeff (d - 1)) -
        AbsoluteDeRham.basicOneForm A 1 (p.1.coeff (d - 2)) := sorry

/-- Example 50.19.4 (3): in degree at least three, the absolute de Rham trace of `t² dt`
has the stated expression in the first three coefficients of `p`. -/
@[stacks 0FLD]
theorem rootSqMulDRoot (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A : Type u} [CommRing A] {d : ℕ} (p : Polynomial.MonicDegreeEq A d) (hd : 2 < d) :
    oneForm r hr (AdjoinRoot.of p.1) (AdjoinRoot.root p.1 ^ 2) (AdjoinRoot.root p.1) =
      -AbsoluteDeRham.basicOneForm A (p.1.coeff (d - 1) ^ 2) (p.1.coeff (d - 1)) +
        AbsoluteDeRham.basicOneForm A (p.1.coeff (d - 1)) (p.1.coeff (d - 2)) +
        AbsoluteDeRham.basicOneForm A (p.1.coeff (d - 2)) (p.1.coeff (d - 1)) -
        AbsoluteDeRham.basicOneForm A 1 (p.1.coeff (d - 3)) := sorry

/-- Example 50.19.4 (4): for `B = A[x]/(x^d-a)`, the absolute de Rham trace of `tⁱ dt`
is zero below `d - 1` and is `da` at `d - 1`. -/
@[stacks 0FLD]
theorem rootPowMulDRootOfBinomial (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A : Type u} [CommRing A] (d : ℕ+) (a : A) (i : Fin (d : ℕ)) :
    oneForm r hr (AdjoinRoot.of (Polynomial.MonicDegreeEq.binomial d a).1)
        (AdjoinRoot.root (Polynomial.MonicDegreeEq.binomial d a).1 ^ i.1)
        (AdjoinRoot.root (Polynomial.MonicDegreeEq.binomial d a).1) =
      if i.1 + 1 = (d : ℕ) then AbsoluteDeRham.basicOneForm A 1 a else 0 := sorry

end Affine
end TraceRule
end RelativeDifferentials
end Scheme
end AlgebraicGeometry
