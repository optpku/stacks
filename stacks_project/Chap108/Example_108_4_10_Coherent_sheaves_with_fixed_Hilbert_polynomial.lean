/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.Numerical
public import stacks_project.Chap108.Example_108_4_10_Coherent_sheaves_with_fixed_Hilbert_polynomial_Hilbert
public import stacks_project.Chap108.Lemma_108_4_8

/-!
# Example 108.4.10 (Coherent sheaves with fixed Hilbert polynomial)

The open-and-closed algebraic substack `Coh^{P,L}_{X/B}` of families whose
fibrewise Euler characteristics agree with a numerical polynomial `P`, and the
disjoint-union decomposition of `Coh_{X/B}` by these loci.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open CategoryTheory.MonoidalCategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Example 108.4.10 (Coherent sheaves with fixed Hilbert polynomial) (1): an
object `(T ⟶ B, F)` of `CohStack f` lies in `hilbert f L P` if and only if
`P n = x.eulerChar (hilbertFamily L (⟨n⟩ : hilbertIndex.{u})) t` for all `n : ℤ` and all
points `t` of `T`. -/
@[stacks 0DNF]
theorem mem_hilbert_iff (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ)
    (hP : IsNumericalPolynomial P) (x : Obj f) :
    hilbert f L P x ↔
      ∀ (n : ℤ) (t : Points (ofOver x.σ.left)),
        x.eulerChar (hilbertFamily L (⟨n⟩ : hilbertIndex.{u})) t = P n :=
  sorry

/-- Example 108.4.10 (Coherent sheaves with fixed Hilbert polynomial) (2): the
inclusion `Hilbert.ι : Coh^{P,L}_{X/B} ⟶ Coh_{X/B}` is an open immersion. -/
@[stacks 0DNF]
instance instOpenImmersion_ι_hilbert (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (L : X.Modules) [isInvertibleObject L]
    (P : ℤ → ℤ) :
    Hom.OpenImmersion (Hilbert.ι f L P) :=
  sorry

/-- Example 108.4.10 (Coherent sheaves with fixed Hilbert polynomial) (3): the
inclusion `Hilbert.ι : Coh^{P,L}_{X/B} ⟶ Coh_{X/B}` is a closed immersion. -/
@[stacks 0DNF]
instance instClosedImmersion_ι_hilbert (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (L : X.Modules) [isInvertibleObject L]
    (P : ℤ → ℤ) :
    Hom.ClosedImmersion (Hilbert.ι f L P) :=
  sorry

/-- Example 108.4.10 (Coherent sheaves with fixed Hilbert polynomial) (4): the
substack `toGroupoidsHilbert f L P` is algebraic. -/
@[stacks 0DNF]
instance instAlgebraicStack_toGroupoidsHilbert (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (L : X.Modules) [isInvertibleObject L]
    (P : ℤ → ℤ) :
    AlgebraicStack (toGroupoidsHilbert f L P) :=
  sorry

/-- Example 108.4.10 (Coherent sheaves with fixed Hilbert polynomial) (5): for
every object `(T ⟶ B, F)` of `CohStack f` and every point `t` of `T`, the
function `n ↦ x.eulerChar (hilbertFamily L (⟨n⟩ : hilbertIndex.{u})) t` is a numerical
polynomial. -/
@[stacks 0DNF]
theorem eulerChar_isNumericalPolynomial (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (L : X.Modules) [isInvertibleObject L] (x : Obj f)
    (t : Points (ofOver x.σ.left)) :
    IsNumericalPolynomial (fun n ↦ x.eulerChar (hilbertFamily L (⟨n⟩ : hilbertIndex.{u})) t) :=
  sorry

/-- Example 108.4.10 (Coherent sheaves with fixed Hilbert polynomial) (6): if the
test scheme of `x` is nonempty, then `x` lies in at most one Hilbert locus
`hilbert f L P` among numerical polynomials `P`. -/
@[stacks 0DNF]
theorem eq_of_mem_hilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (L : X.Modules) [isInvertibleObject L] (P Q : ℤ → ℤ)
    (hP : IsNumericalPolynomial P) (hQ : IsNumericalPolynomial Q) (x : Obj f)
    (hT : Nonempty (Points (ofOver x.σ.left))) (hxP : hilbert f L P x)
    (hxQ : hilbert f L Q x) : P = Q :=
  sorry

/-- Example 108.4.10 (Coherent sheaves with fixed Hilbert polynomial) (7): if the
test scheme of `x` is connected, then `x` lies in `hilbert f L P` for some
numerical polynomial `P`. -/
@[stacks 0DNF]
theorem exists_mem_hilbert_of_isConnected (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (L : X.Modules) [isInvertibleObject L] (x : Obj f)
    [ConnectedSpace x.σ.left.left] :
    ∃ P : ℤ → ℤ, IsNumericalPolynomial P ∧ hilbert f L P x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
