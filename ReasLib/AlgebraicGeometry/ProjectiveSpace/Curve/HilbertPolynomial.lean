/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Logic.Pairwise
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.StructureSheaf
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial
public import ReasLib.AlgebraicGeometry.Scheme.Module.ResidueFieldSkyscraper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

/-- The constant term of the linear Hilbert polynomial of an integral projective curve
over an algebraically closed field is at most one. -/
@[stacks 0DCI]
theorem hilbertPolynomial_const_le_one
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) (hn : 2 ≤ n)
    (C : (scheme k n).IdealSheafData) [IsIntegral C.subscheme]
    (hdim : topologicalKrullDim C.subscheme = 1) (d : ℕ) (e : ℤ)
    (hP : IsHilbertPolynomial k n (pushforwardStructureSheaf k n C)
      (Polynomial.C (d : ℚ) * X + Polynomial.C (e : ℚ))) :
    e ≤ 1 := sorry

/-- A short exact sequence from the structure sheaf of an integral projective curve to
its degree-one twist, with quotient the residue-field skyscrapers at distinct closed points,
has as many quotient points as the leading coefficient of the curve's Hilbert polynomial. -/
@[stacks 0DCI]
theorem transverseSection_card_eq_degree
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) (hn : 2 ≤ n)
    (C : (scheme k n).IdealSheafData) [IsIntegral C.subscheme]
    (hdim : topologicalKrullDim C.subscheme = 1) (d : ℕ) (e : ℤ)
    (hP : IsHilbertPolynomial k n (pushforwardStructureSheaf k n C)
      (Polynomial.C (d : ℚ) * X + Polynomial.C (e : ℚ)))
    (r : ℕ) (c : Fin r → C.subscheme)
    (hc_closed : ∀ i, c i ∈ closedPoints C.subscheme)
    (hc_distinct : Pairwise fun i j ↦ c i ≠ c j)
    (mul : twist k n (pushforwardStructureSheaf k n C) 0 ⟶
      twist k n (pushforwardStructureSheaf k n C) 1)
    (quot : twist k n (pushforwardStructureSheaf k n C) 1 ⟶
      Scheme.Modules.residueFieldSkyscraperCoproduct (fun i ↦ C.subschemeι (c i)))
    (hw : mul ≫ quot = 0)
    (hSE : (ShortComplex.mk mul quot hw).ShortExact) :
    r = d := sorry

/-- For an integral projective curve of degree `d`, exact quotient sequences from each
integral twist to residue-field skyscrapers at `d` distinct closed points induce surjective
maps on global sections in every degree at least `d - 1`. -/
@[stacks 0DCI]
theorem transverseSection_quot_surjective
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) (hn : 2 ≤ n)
    (C : (scheme k n).IdealSheafData) [IsIntegral C.subscheme]
    (hdim : topologicalKrullDim C.subscheme = 1) (d : ℕ) (e : ℤ)
    (hP : IsHilbertPolynomial k n (pushforwardStructureSheaf k n C)
      (Polynomial.C (d : ℚ) * X + Polynomial.C (e : ℚ)))
    (c : Fin d → C.subscheme)
    (hc_closed : ∀ i, c i ∈ closedPoints C.subscheme)
    (hc_distinct : Pairwise fun i j ↦ c i ≠ c j)
    (mul : ∀ t : ℤ,
      twist k n (pushforwardStructureSheaf k n C) (t - 1) ⟶
        twist k n (pushforwardStructureSheaf k n C) t)
    (quot : ∀ t : ℤ,
      twist k n (pushforwardStructureSheaf k n C) t ⟶
        Scheme.Modules.residueFieldSkyscraperCoproduct (fun i ↦ C.subschemeι (c i)))
    (hw : ∀ t, mul t ≫ quot t = 0)
    (hSE : ∀ t, (ShortComplex.mk (mul t) (quot t) (hw t)).ShortExact) :
    ∀ t : ℤ, (d : ℤ) - 1 ≤ t →
      Function.Surjective (Scheme.Modules.globalSectionsMap (quot t)).hom := sorry

/-- The constant term of the linear Hilbert polynomial of an integral projective curve
of degree `d` over an algebraically closed field is at least `2 * d - d ^ 2`. -/
@[stacks 0DCI]
theorem hilbertPolynomial_const_ge
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) (hn : 2 ≤ n)
    (C : (scheme k n).IdealSheafData) [IsIntegral C.subscheme]
    (hdim : topologicalKrullDim C.subscheme = 1) (d : ℕ) (e : ℤ)
    (hP : IsHilbertPolynomial k n (pushforwardStructureSheaf k n C)
      (Polynomial.C (d : ℚ) * X + Polynomial.C (e : ℚ))) :
    2 * (d : ℤ) - (d : ℤ) ^ 2 ≤ e := sorry

end AlgebraicGeometry.ProjectiveSpace
