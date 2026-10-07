module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap95.«95_18_2_1_Stack»
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Lemma 97.14.2

If `S` is a scheme and `F : 𝒳 ⟶ 𝒴` is a 1-morphism of stacks in groupoids
over `(Sch/S)_fppf` such that `𝒳` is representable by an algebraic space, and
`F` is representable by algebraic spaces, surjective, flat, and locally of
finite presentation, then the finite Hilbert stack `H_d(𝒳/𝒴)` is an
algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

/-- Lemma 97.14.2: if `S` is a scheme and `F : 𝒳 ⟶ 𝒴` is a 1-morphism of
stacks in groupoids over `(Sch/S)_fppf` such that `𝒳` is representable by an
algebraic space, and `F` is representable by algebraic spaces, surjective,
flat, and locally of finite presentation, then the finite Hilbert stack
`H_d(𝒳/𝒴)` is an algebraic stack. The hypotheses `Surjective`, `Flat`, and
`LocallyOfFinitePresentation` each include relative representability by
algebraic spaces. -/
@[stacks 06CI]
theorem algebraicStack_ofRelativeSpace {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
    (F : 𝒳 ⟶ 𝒴) (hX : IsRepresentableByAlgebraicSpace (asGroupoidsOver 𝒳))
    (d : ℕ) [NeZero d]
    [Groupoids.Hom.Surjective (asGroupoidsOverMor F)]
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] :
    AlgebraicStack (stack (asGroupoidsOverMor F) d).toGroupoids :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
