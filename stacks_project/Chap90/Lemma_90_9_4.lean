module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory.Versal

/-!
# Unobstructed predeformation categories and versal bases

Source bridge for the versal-base unobstructedness criteria.
-/

@[expose] public section

open CategoryTheory IsLocalRing ArtinianLocalAlgCat CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/- Lemma 90.9.4 -/
@[stacks 0DZK]
#check (CategoryTheory.Functor.isUnobstructed_iff_formallySmooth :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type (u + 1)} [Category.{u + 1} F]
    {p : F ⥤ ArtinianLocalAlgCat Λ k} [IsPredeformationCategory p]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ],
    Functor.IsUnobstructed p ↔
      (algebraMap Λ ξ.base.carrier).formally_smooth_for_adic
        (maximalIdeal ξ.base.carrier))

@[stacks 0DZK]
#check (CategoryTheory.Functor.isUnobstructed_tfae_isClassical :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type (u + 1)} [Category.{u + 1} F]
    {p : F ⥤ ArtinianLocalAlgCat Λ k} [IsPredeformationCategory p] [IsClassical Λ k]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ],
    List.TFAE
      [Functor.IsUnobstructed p,
        (algebraMap Λ ξ.base.carrier).formally_smooth_for_adic
          (maximalIdeal ξ.base.carrier),
        IsPowerSeriesOver (fromClassical ξ.base)])

#check (CategoryTheory.Functor.isUnobstructed_iff_isPowerSeriesOver :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type (u + 1)} [Category.{u + 1} F]
    {p : F ⥤ ArtinianLocalAlgCat Λ k} [IsPredeformationCategory p] [IsClassical Λ k]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ],
    Functor.IsUnobstructed p ↔ IsPowerSeriesOver (fromClassical ξ.base))

end CategoryTheory.Functor
