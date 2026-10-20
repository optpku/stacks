module

public import ReasLib.CategoryTheory.Functor.Algebraic.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

/- The source conclusion is already the most useful source-facing layer. The canonical
`Subobject.Factors` API requires first deriving `Mono g` and then replacing `g` by
`Subobject.mk g`, so the labeled entry retains the existential factorization. The neutral support
also exposes `subobjectFactorsOfRangeSubset` and the same conclusion under only the categorical
hypotheses used by its proof. -/

section

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

/- Lemma 6.15.4: if `F.map g` is injective and the range of `F.map f` is contained in the range
of `F.map g`, then `f` factors through `g`. -/
@[stacks 007P]
#check IsAlgebraicStructure.morphism_factors_through_of_range_subset_of_injective F

end
