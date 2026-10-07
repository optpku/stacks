module

public import stacks_project.Chap94.Lemma_94_9_9_Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

variable {S : Scheme.{u}}
variable {X Y Z : GroupoidsOver S}
variable {f : X ⟶ Y} {g : Y ⟶ Z}
variable (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hg : relativelyRepresentableByAlgebraicSpaces g)

/- Lemma 94.9.9: let `S` be a scheme contained in `Sch_fppf`. Let `X`, `Y`, `Z`
be categories fibred in groupoids over `(Sch/S)_fppf`. If `f : X ⟶ Y` and
`g : Y ⟶ Z` are 1-morphisms representable by algebraic spaces, then the
composite `f ≫ g : X ⟶ Z` is a 1-morphism representable by algebraic spaces. -/
@[stacks 0301]
#check (relativelyRepresentableByAlgebraicSpaces.comp_mem hf hg :
    relativelyRepresentableByAlgebraicSpaces (f ≫ g))
