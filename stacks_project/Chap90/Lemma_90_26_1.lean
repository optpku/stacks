/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothKernelPair
import StacksCheckRecall

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

/- Lemma 90.26.1 (1): if `f : U ⟶ F` is a smooth morphism of categories cofibered in
groupoids over `ArtinianLocalAlgCat Λ k`, with `U` a set-valued functor, then the
kernel-pair groupoid `ofMorphism f` constructed in Lemma 90.25.2 is smooth. -/
@[stacks 06L1] #check (CategoryTheory.GroupoidInFunctors.instIsSmooth_ofMorphism :
  ∀ (f : Functor.ofTypeValued U ⟶ F)
    [BasedFunctor.IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor f)],
    CategoryTheory.GroupoidInFunctors.IsSmooth
      (CategoryTheory.GroupoidInFunctors.ofMorphism f).s
      (CategoryTheory.GroupoidInFunctors.ofMorphism f).t)

#check (CategoryTheory.GroupoidInFunctors.instNatTransIsSmooth_ofMorphism_s :
  ∀ (f : Functor.ofTypeValued U ⟶ F)
    [BasedFunctor.IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor f)],
    NatTrans.IsSmooth (CategoryTheory.GroupoidInFunctors.ofMorphism f).s)

#check (CategoryTheory.GroupoidInFunctors.instNatTransIsSmooth_ofMorphism_t :
  ∀ (f : Functor.ofTypeValued U ⟶ F)
    [BasedFunctor.IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor f)],
    NatTrans.IsSmooth (CategoryTheory.GroupoidInFunctors.ofMorphism f).t)

/- Lemma 90.26.1 (2): if `f : U ⟶ F` is a smooth morphism of categories cofibered in
groupoids over `ArtinianLocalAlgCat Λ k` and the residue-fibre functor
`(toBasedFunctor f).fiberFunctor (residue Λ k)` is essentially surjective, then
`quotientMap f`, the morphism `[U/R] ⟶ F` of Lemma 90.25.3, is an equivalence. -/
@[stacks 06L1] #check
  (CategoryTheory.GroupoidInFunctors.quotientMap_isEquivalence_of_residueEssSurj :
  ∀ (f : Functor.ofTypeValued U ⟶ F)
    [BasedFunctor.IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor f)]
    [((CofiberedCategoryOver.Groupoids.toBasedFunctor f).fiberFunctor
        (ArtinianLocalAlgCat.residue Λ k)).EssSurj],
    BasedFunctor.IsEquivalence (CategoryTheory.GroupoidInFunctors.quotientMap f))
