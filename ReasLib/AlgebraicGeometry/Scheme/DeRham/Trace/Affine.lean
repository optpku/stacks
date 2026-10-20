/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Polynomial.MonicDegreeEq
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.AdjoinRoot
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.AffineForms
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Trace

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.Affine

/-- The degree-one absolute de Rham trace evaluated on the affine form `b₀ db₁`. -/
noncomputable def oneForm (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    [IsFinite (Spec.map (CommRingCat.ofHom φ))]
    [Syntomic (Spec.map (CommRingCat.ofHom φ))] (b₀ b₁ : B) :
    (RingedSpace.DeRham.term
      (terminal.from (Spec (CommRingCat.of A))).toLRSHom.toShHom 1).val.obj
        (Opposite.op ⊤) :=
  (((TraceRule.complexMap r hr (Spec.map (CommRingCat.ofHom φ))).f 1).val.app
      (Opposite.op ⊤)).hom (AbsoluteDeRham.basicOneForm B b₀ b₁)

/-- `oneForm` is evaluation of the degree-one component of `TraceRule.complexMap` on the
canonical affine basic form. -/
theorem oneForm_apply (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    [IsFinite (Spec.map (CommRingCat.ofHom φ))]
    [Syntomic (Spec.map (CommRingCat.ofHom φ))] (b₀ b₁ : B) :
    oneForm r hr φ b₀ b₁ =
      (((TraceRule.complexMap r hr (Spec.map (CommRingCat.ofHom φ))).f 1).val.app
        (Opposite.op ⊤)).hom (AbsoluteDeRham.basicOneForm B b₀ b₁) := rfl

/-- The absolute de Rham trace of the distinguished root differential is minus the
differential of the coefficient of degree `d - 1` for a monic polynomial of positive degree. -/
theorem dRoot (r : TraceRule.{u}) (hr : IsTraceRule r) {A : Type u} [CommRing A]
    {d : ℕ} (p : Polynomial.MonicDegreeEq A d) (hd : 0 < d) :
    oneForm r hr (AdjoinRoot.of p.1) 1 (AdjoinRoot.root p.1) =
      -AbsoluteDeRham.basicOneForm A 1 (p.1.coeff (d - 1)) := sorry

/-- For a monic polynomial of degree at least two with first coefficients `a₁` and `a₂`,
the absolute de Rham trace of `t dt` is `a₁ da₁ - da₂`. -/
theorem rootMulDRoot (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A : Type u} [CommRing A] {d : ℕ} (p : Polynomial.MonicDegreeEq A d) (hd : 1 < d) :
    oneForm r hr (AdjoinRoot.of p.1) (AdjoinRoot.root p.1) (AdjoinRoot.root p.1) =
      AbsoluteDeRham.basicOneForm A (p.1.coeff (d - 1)) (p.1.coeff (d - 1)) -
        AbsoluteDeRham.basicOneForm A 1 (p.1.coeff (d - 2)) := sorry

/-- For a monic polynomial of degree at least three with first coefficients `a₁`, `a₂`,
and `a₃`, the absolute de Rham trace of `t² dt` is
`-a₁² da₁ + a₁ da₂ + a₂ da₁ - da₃`. -/
theorem rootSqMulDRoot (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A : Type u} [CommRing A] {d : ℕ} (p : Polynomial.MonicDegreeEq A d) (hd : 2 < d) :
    oneForm r hr (AdjoinRoot.of p.1) (AdjoinRoot.root p.1 ^ 2) (AdjoinRoot.root p.1) =
      -AbsoluteDeRham.basicOneForm A (p.1.coeff (d - 1) ^ 2) (p.1.coeff (d - 1)) +
        AbsoluteDeRham.basicOneForm A (p.1.coeff (d - 1)) (p.1.coeff (d - 2)) +
        AbsoluteDeRham.basicOneForm A (p.1.coeff (d - 2)) (p.1.coeff (d - 1)) -
        AbsoluteDeRham.basicOneForm A 1 (p.1.coeff (d - 3)) := sorry

/-- For the quotient by `X ^ d - C a`, the absolute de Rham trace of `tⁱ dt` is zero
for `i < d - 1` and is `da` for `i = d - 1`. -/
theorem rootPowMulDRootOfBinomial (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A : Type u} [CommRing A] (d : ℕ+) (a : A) (i : Fin (d : ℕ)) :
    oneForm r hr (AdjoinRoot.of (Polynomial.MonicDegreeEq.binomial d a).1)
        (AdjoinRoot.root (Polynomial.MonicDegreeEq.binomial d a).1 ^ i.1)
        (AdjoinRoot.root (Polynomial.MonicDegreeEq.binomial d a).1) =
      if i.1 + 1 = (d : ℕ) then AbsoluteDeRham.basicOneForm A 1 a else 0 := sorry


end AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.Affine
