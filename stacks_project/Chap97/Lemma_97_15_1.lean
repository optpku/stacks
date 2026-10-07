module

public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap97.Lemma_97_15_4_Lci
public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Lemma 97.15.1

If `F : 𝒳 ⟶ 𝒴` is a 1-morphism of stacks in groupoids over `(Sch/S)_fppf`
that is representable by algebraic spaces, flat, and locally of finite
presentation, then `H_{d,lci}(𝒳/𝒴)` is a stack in groupoids and the
inclusion `H_{d,lci}(𝒳/𝒴) ⟶ H_d(𝒳/𝒴)` is representable by algebraic
spaces and an open immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- Lemma 97.15.1 (1): if `F : 𝒳 ⟶ 𝒴` is a 1-morphism of stacks in groupoids
over `(Sch/S)_fppf` that is representable by algebraic spaces, flat, and
locally of finite presentation, then the restricted projection of
`H_{d,lci}(𝒳/𝒴)` is a stack in groupoids over `(Sch/S)_fppf`. The
hypotheses `Flat` and `LocallyOfFinitePresentation` each include relative
representability by algebraic spaces. -/
@[stacks 06CL, instance]
instance lciP.isStack (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (lciP F d) :=
  sorry

/-- Lemma 97.15.1 (2): in the same situation, the inclusion functor
`H_{d,lci}(𝒳/𝒴) ⟶ H_d(𝒳/𝒴)` is representable by algebraic spaces and an
open immersion. -/
@[stacks 06CL, instance]
instance lciInclusion.openImmersion (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] :
    Groupoids.Hom.OpenImmersion (asGroupoidsOverMor (lciInclusion F d)) :=
  sorry

/-- The inclusion of the LCI Hilbert stack is representable by algebraic
spaces. -/
theorem lciInclusion.relativelyRepresentable (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] :
    relativelyRepresentableByAlgebraicSpaces
      (asGroupoidsOverMor (lciInclusion F d)) :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
