module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Trace.Affine

@[expose] public section

open AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.RelativeDifferentials
open AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.Affine
open scoped Polynomial

universe u

/- Example 50.19.4 (1): the trace of `dt`. -/
@[stacks 0FLD] #check (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.Affine.dRoot :
  ∀ (r : TraceRule.{u}) (hr : IsTraceRule r) {A : Type u} [CommRing A]
    {d : ℕ} (p : Polynomial.MonicDegreeEq A d) (hd : 0 < d),
    oneForm r hr (AdjoinRoot.of p.1) 1 (AdjoinRoot.root p.1) =
      -AbsoluteDeRham.basicOneForm A 1 (p.1.coeff (d - 1)))

/- Example 50.19.4 (2): the trace of `t dt`. -/
@[stacks 0FLD] #check (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.Affine.rootMulDRoot :
  ∀ (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A : Type u} [CommRing A] {d : ℕ} (p : Polynomial.MonicDegreeEq A d) (hd : 1 < d),
    oneForm r hr (AdjoinRoot.of p.1) (AdjoinRoot.root p.1) (AdjoinRoot.root p.1) =
      AbsoluteDeRham.basicOneForm A (p.1.coeff (d - 1)) (p.1.coeff (d - 1)) -
        AbsoluteDeRham.basicOneForm A 1 (p.1.coeff (d - 2)))

/- Example 50.19.4 (3): the trace of `t² dt`. -/
@[stacks 0FLD] #check (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.Affine.rootSqMulDRoot :
  ∀ (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A : Type u} [CommRing A] {d : ℕ} (p : Polynomial.MonicDegreeEq A d) (hd : 2 < d),
    oneForm r hr (AdjoinRoot.of p.1) (AdjoinRoot.root p.1 ^ 2) (AdjoinRoot.root p.1) =
      -AbsoluteDeRham.basicOneForm A (p.1.coeff (d - 1) ^ 2) (p.1.coeff (d - 1)) +
        AbsoluteDeRham.basicOneForm A (p.1.coeff (d - 1)) (p.1.coeff (d - 2)) +
        AbsoluteDeRham.basicOneForm A (p.1.coeff (d - 2)) (p.1.coeff (d - 1)) -
        AbsoluteDeRham.basicOneForm A 1 (p.1.coeff (d - 3)))

/- Example 50.19.4 (4): the binomial trace formula. -/
@[stacks 0FLD] #check (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.Affine.rootPowMulDRootOfBinomial :
  ∀ (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A : Type u} [CommRing A] (d : ℕ+) (a : A) (i : Fin (d : ℕ)),
    oneForm r hr (AdjoinRoot.of (Polynomial.MonicDegreeEq.binomial d a).1)
        (AdjoinRoot.root (Polynomial.MonicDegreeEq.binomial d a).1 ^ i.1)
        (AdjoinRoot.root (Polynomial.MonicDegreeEq.binomial d a).1) =
      if i.1 + 1 = (d : ℕ) then AbsoluteDeRham.basicOneForm A 1 a else 0)

