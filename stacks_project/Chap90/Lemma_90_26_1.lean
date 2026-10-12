/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Definition_90_16_8_Predeformation
public import stacks_project.Chap90.Definition_90_23_1
public import stacks_project.Chap90.Lemma_90_25_2
public import stacks_project.Chap90.Lemma_90_25_3_QuotientMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smooth kernel-pair presentations

A smooth morphism `f : U ⟶ F` of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` yields a smooth kernel-pair groupoid, and if the
residue-fibre map is essentially surjective then the quotient morphism is an
equivalence.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {U : ArtinianLocalAlgCat Λ k ⥤ Type (max u v)}
variable {F : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) (max u v), u}
    (ArtinianLocalAlgCat Λ k)}

namespace CategoryTheory.GroupoidInFunctors

/-- Lemma 90.26.1 (1): if `f : U ⟶ F` is a smooth morphism of categories cofibered in
groupoids over `ArtinianLocalAlgCat Λ k`, with `U` a set-valued functor, then the
kernel-pair groupoid `ofMorphism f` constructed in Lemma 90.25.2 is smooth. -/
@[stacks 06L1]
instance instIsSmooth_ofMorphism (f : Functor.ofTypeValued U ⟶ F)
    [BasedFunctor.IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor f)] :
    IsSmooth (ofMorphism f).s (ofMorphism f).t := sorry

/-- The source map of the kernel-pair groupoid of a smooth morphism is smooth. -/
instance instNatTransIsSmooth_ofMorphism_s (f : Functor.ofTypeValued U ⟶ F)
    [BasedFunctor.IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor f)] :
    NatTrans.IsSmooth (ofMorphism f).s := sorry

/-- The target map of the kernel-pair groupoid of a smooth morphism is smooth. -/
instance instNatTransIsSmooth_ofMorphism_t (f : Functor.ofTypeValued U ⟶ F)
    [BasedFunctor.IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor f)] :
    NatTrans.IsSmooth (ofMorphism f).t := sorry

/-- Lemma 90.26.1 (2): if `f : U ⟶ F` is a smooth morphism of categories cofibered in
groupoids over `ArtinianLocalAlgCat Λ k` and the residue-fibre functor
`(toBasedFunctor f).fiberFunctor (residue Λ k)` is essentially surjective, then
`quotientMap f`, the morphism `[U/R] ⟶ F` of Lemma 90.25.3, is an equivalence. -/
@[stacks 06L1]
instance quotientMap_isEquivalence_of_residueEssSurj (f : Functor.ofTypeValued U ⟶ F)
    [BasedFunctor.IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor f)]
    [((CofiberedCategoryOver.Groupoids.toBasedFunctor f).fiberFunctor
        (ArtinianLocalAlgCat.residue Λ k)).EssSurj] :
    BasedFunctor.IsEquivalence (quotientMap f) := sorry

end CategoryTheory.GroupoidInFunctors
