/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Curve.HilbertPolynomial
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

/- Exercise 111.45.5 (1): In Situation 111.45.1, with `2 ≤ n` and `k` algebraically
closed, if `C` is an integral closed subscheme of dimension `1` in `scheme k n` and
`Polynomial.C (d : ℚ) * X + Polynomial.C (e : ℚ)` is the Hilbert polynomial of
`i_* 𝒪_C`, then `e ≤ 1`. -/
@[stacks 0DCI]
#check (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial_const_le_one :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) (hn : 2 ≤ n)
    (C : (scheme k n).IdealSheafData) [IsIntegral C.subscheme]
    (hdim : topologicalKrullDim C.subscheme = 1) (d : ℕ) (e : ℤ)
    (hP : IsHilbertPolynomial k n (pushforwardStructureSheaf k n C)
      (Polynomial.C (d : ℚ) * X + Polynomial.C (e : ℚ))),
    e ≤ 1)

/- Exercise 111.45.5 (2): If a hyperplane section of `𝒪(1)` meets `C` in pairwise
distinct closed points and yields a short exact sequence
`0 ⟶ 𝒪_C ⟶ 𝒪_C(1) ⟶ ∐ k_{c_i} ⟶ 0` of modules on `scheme k n`, then the number
of those points equals the leading coefficient `d`. -/
@[stacks 0DCI]
#check (AlgebraicGeometry.ProjectiveSpace.transverseSection_card_eq_degree :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) (hn : 2 ≤ n)
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
    (hSE : (ShortComplex.mk mul quot hw).ShortExact),
    r = d)

/- Exercise 111.45.5 (3): Twisting the transversal hyperplane-section sequence
induces maps `φ_t : Γ(𝒪_C(t)) ⟶ Γ(∐ k_{c_i})`, and these maps are surjective for
`t ≥ d - 1`. -/
@[stacks 0DCI]
#check (AlgebraicGeometry.ProjectiveSpace.transverseSection_quot_surjective :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) (hn : 2 ≤ n)
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
    (hSE : ∀ t, (ShortComplex.mk (mul t) (quot t) (hw t)).ShortExact),
    ∀ t : ℤ, (d : ℤ) - 1 ≤ t →
      Function.Surjective (Scheme.Modules.globalSectionsMap (quot t)).hom)

/- Exercise 111.45.5 (4): In the same situation, the constant term of the Hilbert
polynomial satisfies `2 * d - d ^ 2 ≤ e`. -/
@[stacks 0DCI]
#check (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial_const_ge :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) (hn : 2 ≤ n)
    (C : (scheme k n).IdealSheafData) [IsIntegral C.subscheme]
    (hdim : topologicalKrullDim C.subscheme = 1) (d : ℕ) (e : ℤ)
    (hP : IsHilbertPolynomial k n (pushforwardStructureSheaf k n C)
      (Polynomial.C (d : ℚ) * X + Polynomial.C (e : ℚ))),
    2 * (d : ℤ) - (d : ℤ) ^ 2 ≤ e)

end AlgebraicGeometry.ProjectiveSpace
