/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory.Predeformation
import StacksCheckRecall

/-!
# Smoothness of predeformation categories along a smooth morphism

If `φ : U → F` is a smooth morphism of predeformation categories over
`ArtinianLocalAlgCat Λ k`, then `F` is smooth if and only if `U` is smooth.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type w} [Category.{v} F] [Category.{v} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}

/- Remark 90.9.2: if `p` and `q` are predeformation categories and
`φ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p` is a smooth morphism,
then by Lemma 90.8.8 `φ` is essentially surjective, so by Lemma 90.8.7 the
structure morphism of `p` is smooth if and only if the composite
`φ ⋙ BasedCategory.toBase (BasedCategory.ofFunctor p)` is smooth, i.e. `p` is
smooth if and only if `q` is smooth. -/
@[stacks 06HQ] #check (CategoryTheory.Functor.isSmooth_iff_of_smooth :
  ∀ [Functor.IsPredeformationCategory p] [Functor.IsPredeformationCategory q]
    (φ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p) [BasedFunctor.IsSmooth φ],
    Functor.IsSmooth p ↔ Functor.IsSmooth q)

universe uC vC uX vX uY vY

#check (CategoryTheory.BasedFunctor.comp_toBase :
  ∀ {C : Type uC} [Category.{vC} C]
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C} (φ : X ⥤ᵇ Y),
    φ ⋙ BasedCategory.toBase Y = BasedCategory.toBase X)

#check (CategoryTheory.BasedFunctor.isSmooth_toBase_iff_comp :
  ∀ [Functor.IsPredeformationCategory p] [Functor.IsPredeformationCategory q]
    (φ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p) [BasedFunctor.IsSmooth φ],
    BasedFunctor.IsSmooth (BasedCategory.toBase (BasedCategory.ofFunctor p)) ↔
      BasedFunctor.IsSmooth (φ ⋙ BasedCategory.toBase (BasedCategory.ofFunctor p)))

#check (CategoryTheory.BasedFunctor.essSurj_of_isPredeformationCategory :
  ∀ [Functor.IsPredeformationCategory p] [Functor.IsPredeformationCategory q]
    (φ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p) [BasedFunctor.IsSmooth φ],
    φ.toFunctor.EssSurj)
