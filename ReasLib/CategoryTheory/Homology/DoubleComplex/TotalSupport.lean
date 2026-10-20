/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.Support
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Total.FiniteSupport
public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import ReasLib.CategoryTheory.ObjectProperty.FiniteCoproductClosure
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Support Properties of Total Complexes

This file connects objectwise support conditions on a cohomological double complex with the
existence, boundedness, and termwise injectivity properties of its coproduct total complex.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape

noncomputable section

universe v u

namespace HomologicalComplex₂

namespace AntidiagonalSupport.Finite

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K : HomologicalComplex₂ C (up ℤ) (up ℤ)}

/-- In a category with finite coproducts, finite antidiagonal support suffices for the coproduct
total complex to exist. -/
@[stacks 0132 "existence of a finite-antidiagonal total complex"]
theorem hasTotal [HasFiniteCoproducts C] (hfin : AntidiagonalSupport.Finite K) :
    K.HasTotal (up ℤ) := sorry

/-- A finite cohomological antidiagonal support predicate is the cohomological specialization of
the shape-polymorphic finite total-degree support predicate. -/
@[stacks 0132 "cohomological support as finite total support"]
theorem toTotalSupport (hfin : AntidiagonalSupport.Finite K) :
    Total.Support.Finite (c := up ℤ) K := sorry

/-- For cohomological double complexes, finite total-degree support is equivalent to finite
antidiagonal support. -/
@[stacks 0132 "finite antidiagonal support characterization"]
theorem iff_totalSupport :
    AntidiagonalSupport.Finite K ↔ Total.Support.Finite (c := up ℤ) K := sorry

/-- A pair of lower bounds forces finite support on every cohomological antidiagonal.  The
outer bound controls the first index, while the uniform inner bound controls the second one. -/
@[stacks 0132 "finite antidiagonal support from lower bounds"]
theorem of_isStrictlyGE {a b : ℤ}
    (h₁ : CochainComplex.IsStrictlyGE K a)
    (h₂ : ∀ p : ℤ, CochainComplex.IsStrictlyGE (K.X p) b) :
    AntidiagonalSupport.Finite K := sorry

/-- In a category with finite coproducts, the lower-bound criterion directly supplies a total
complex. -/
@[stacks 0132 "totalization from lower bounds"]
theorem hasTotal_of_isStrictlyGE [HasFiniteCoproducts C]
    {a b : ℤ} (h₁ : CochainComplex.IsStrictlyGE K a)
    (h₂ : ∀ p : ℤ, CochainComplex.IsStrictlyGE (K.X p) b) :
    K.HasTotal (up ℤ) :=
  hasTotal (of_isStrictlyGE h₁ h₂)

end AntidiagonalSupport.Finite

section Boundedness

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K : HomologicalComplex₂ C (up ℤ) (up ℤ)}
variable [K.HasTotal (up ℤ)]

namespace Total

/-- If a double complex is bounded below by `a` in the first direction and uniformly bounded
below by `b` in the second direction, then its total complex is bounded below by `a + b`. -/
@[stacks 0132 "boundedness of a total complex"]
theorem isStrictlyGE (a b : ℤ) (h₁ : CochainComplex.IsStrictlyGE K a)
    (h₂ : ∀ p : ℤ, CochainComplex.IsStrictlyGE (K.X p) b) :
    CochainComplex.IsStrictlyGE (K.total (up ℤ)) (a + b) := sorry

end Total

end Boundedness

namespace Total

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : HomologicalComplex₂ C (up ℤ) (up ℤ)} [K.HasTotal (up ℤ)]

/-- A finite-antidiagonal total complex whose bidegree objects are injective is termwise
injective. This is the cohomological facade of `Total.Support.Finite.injective`. -/
@[stacks 0132 "termwise injectivity of a finite-support total complex"]
theorem injective_of_finite_support
    (hfin : AntidiagonalSupport.Finite K)
    (hinj : ∀ p q : ℤ, Injective ((K.X p).X q)) (n : ℤ) :
    Injective ((K.total (up ℤ)).X n) := sorry

/-- A finite-support total complex inherits any object property stable under zero objects,
isomorphisms, and finite coproducts from its bidegree terms. -/
@[stacks 0132 "termwise properties of finite-support totals"]
theorem termsIn
    (P : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderFiniteCoproducts]
    (hfin : AntidiagonalSupport.Finite K)
    (hP : ∀ p q : ℤ, P ((K.X p).X q)) :
    CochainComplex.termsIn P (K.total (up ℤ)) := sorry

end Total

end HomologicalComplex₂
