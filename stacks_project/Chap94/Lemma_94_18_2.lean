module

public import stacks_project.Chap94.Lemma_94_18_2_InverseImage
public import stacks_project.Chap94.Lemma_94_18_2_OnSlice
import StacksCheckRecall

/-!
# Lemma 94.18.2

Change of big site for algebraic stacks: inverse image along a fully faithful
enlargement of fppf sites is a 2-functor on algebraic stacks inducing Hom-category
equivalences, and the essential image is characterized by presentations coming from
`Spaces / S`.
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.AlgebraicStacksOnSlice

/- Lemma 94.18.2 (1): suppose `Sch_fppf` is contained in `Sch'_fppf`. Let `S` be an
object of `Sch_fppf`. Write `AlgebraicStacksOnSlice ι J S` for the 2-category of
algebraic stacks over `S` defined using `Sch_fppf`, and `AlgebraicStacks (ι.obj S)`
for those defined using `Sch'_fppf`. The rule `X ↦ f⁻¹X` of Lemma 94.18.1 defines a
functor of 2-categories `AlgebraicStacksOnSlice ι J S ⟶ AlgebraicStacks (ι.obj S)`
which induces equivalences of morphism categories
`(X ⟶ Y) ⥤ (inverseImage X ⟶ inverseImage Y)` for every pair of objects. -/
@[stacks 04X3]
#check AlgebraicGeometry.AlgebraicStacksOnSlice.inverseImage.mapFunctor.isEquivalence

end AlgebraicGeometry.AlgebraicStacksOnSlice

namespace AlgebraicGeometry.AlgebraicStacks

/- Lemma 94.18.2 (2): in the same setup, an object `X'` of
`AlgebraicStacks (ι.obj S)` is equivalent to `f⁻¹X` for some
`X` in `AlgebraicStacksOnSlice ι J S` if and only if it has a presentation
`[U' / R']` with `U', R'` isomorphic to `f⁻¹U`, `f⁻¹R` for some
`U, R` in `Spaces / S`. -/
@[stacks 04X3]
#check AlgebraicGeometry.AlgebraicStacks.essentiallyInImage_iff

end AlgebraicGeometry.AlgebraicStacks
