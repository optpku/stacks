/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothGroupoid
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue
public import ReasLib.CategoryTheory.Groupoid.KernelPair.Quotient
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber

/-!
# Smooth kernel-pair presentations

A smooth morphism from a set-valued functor to a category cofibered in groupoids
has a smooth kernel-pair groupoid. If its residue-fibre functor is essentially
surjective, the canonical morphism from the kernel-pair quotient is an equivalence.
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

/-- The kernel-pair groupoid of a smooth morphism from a set-valued functor to a
category cofibered in groupoids over Artinian local algebras is smooth. -/
theorem instIsSmooth_ofMorphism (f : Functor.ofTypeValued U ⟶ F)
    [BasedFunctor.IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor f)] :
    IsSmooth (ofMorphism f).s (ofMorphism f).t := sorry

/-- The source map of the kernel-pair groupoid of a smooth morphism is smooth. -/
theorem instNatTransIsSmooth_ofMorphism_s (f : Functor.ofTypeValued U ⟶ F)
    [BasedFunctor.IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor f)] :
    NatTrans.IsSmooth (ofMorphism f).s :=
  (instIsSmooth_ofMorphism f).isSmooth_s

/-- The target map of the kernel-pair groupoid of a smooth morphism is smooth. -/
theorem instNatTransIsSmooth_ofMorphism_t (f : Functor.ofTypeValued U ⟶ F)
    [BasedFunctor.IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor f)] :
    NatTrans.IsSmooth (ofMorphism f).t :=
  (instIsSmooth_ofMorphism f).isSmooth_t

/-- A smooth morphism from a set-valued functor to a category cofibered in groupoids
that is essentially surjective on the residue fibre induces an equivalence from its
kernel-pair quotient to the target category. -/
theorem quotientMap_isEquivalence_of_residueEssSurj (f : Functor.ofTypeValued U ⟶ F)
    [BasedFunctor.IsSmooth (CofiberedCategoryOver.Groupoids.toBasedFunctor f)]
    [((CofiberedCategoryOver.Groupoids.toBasedFunctor f).fiberFunctor
        (ArtinianLocalAlgCat.residue Λ k)).EssSurj] :
    BasedFunctor.IsEquivalence (quotientMap f) := sorry

end CategoryTheory.GroupoidInFunctors
