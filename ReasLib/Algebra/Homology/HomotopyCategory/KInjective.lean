/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Injectivity in Homotopy Triangles

This leaf specializes the triangulated closure of a right orthogonal to
K-injective cochain complexes. The generic closure theorem remains owned by
`ObjectProperty.rightOrthogonal`; these bridges avoid repeatedly unfolding the
K-injective/right-orthogonal characterization in homotopy-category arguments.
-/

open CategoryTheory
open CategoryTheory.Pretriangulated
open ComplexShape

universe v u

namespace CochainComplex.IsKInjective

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Lemma 13.31.3 (Stacks 090X) (1): in a distinguished homotopy triangle,
K-injectivity of the first two vertices implies K-injectivity of the third. -/
@[stacks 090X]
theorem of_distinguishedTriangle_obj₁_obj₂
    (T : Triangle (HomotopyCategory A (up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory A (up ℤ)))
    (h₁ : CochainComplex.IsKInjective T.obj₁.as)
    (h₂ : CochainComplex.IsKInjective T.obj₂.as) :
    CochainComplex.IsKInjective T.obj₃.as := sorry

/-- Lemma 13.31.3 (Stacks 090X) (2): in a distinguished homotopy triangle,
K-injectivity of the first and third vertices implies K-injectivity of the second. -/
@[stacks 090X]
theorem of_distinguishedTriangle_obj₁_obj₃
    (T : Triangle (HomotopyCategory A (up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory A (up ℤ)))
    (h₁ : CochainComplex.IsKInjective T.obj₁.as)
    (h₃ : CochainComplex.IsKInjective T.obj₃.as) :
    CochainComplex.IsKInjective T.obj₂.as := sorry

/-- Lemma 13.31.3 (Stacks 090X) (3): in a distinguished homotopy triangle,
K-injectivity of the second and third vertices implies K-injectivity of the first. -/
@[stacks 090X]
theorem of_distinguishedTriangle_obj₂_obj₃
    (T : Triangle (HomotopyCategory A (up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory A (up ℤ)))
    (h₂ : CochainComplex.IsKInjective T.obj₂.as)
    (h₃ : CochainComplex.IsKInjective T.obj₃.as) :
    CochainComplex.IsKInjective T.obj₁.as := sorry

end CochainComplex.IsKInjective
