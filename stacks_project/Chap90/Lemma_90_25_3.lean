module

public import stacks_project.Chap90.Lemma_90_25_3_QuotientMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# The canonical morphism from a kernel-pair presentation

A morphism `f : U ⟶ F` of categories cofibered in groupoids yields a fully faithful
morphism `[f] : [U/R] ⟶ F` over `C`, which is an equivalence if and only if `f` is
essentially surjective.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]
variable {U : C ⥤ Type (max v w)}
variable {F : CofiberedCategoryOver.Groupoids.{u, v, max u (max v w), v} C}

/-- Lemma 90.25.3 (1): the canonical morphism `[f] : [U/R] ⟶ F` associated to a morphism
`f : U ⟶ F` of categories cofibered in groupoids, with kernel-pair groupoid
`ofMorphism f`, is fully faithful. -/
@[stacks 06KZ]
theorem quotientMap_fullyFaithful (f : Functor.ofTypeValued U ⟶ F) :
    Nonempty (quotientMap f).FullyFaithful := sorry

/-- Lemma 90.25.3 (2): the canonical morphism `[f] : [U/R] ⟶ F` is an equivalence of
categories cofibered in groupoids if and only if `f : U ⟶ F` is essentially
surjective. -/
@[stacks 06KZ]
theorem quotientMap_isEquivalence_iff (f : Functor.ofTypeValued U ⟶ F) :
    BasedFunctor.IsEquivalence (quotientMap f) ↔
      (CofiberedCategoryOver.Groupoids.toBasedFunctor f).EssSurj := sorry

end CategoryTheory.GroupoidInFunctors
