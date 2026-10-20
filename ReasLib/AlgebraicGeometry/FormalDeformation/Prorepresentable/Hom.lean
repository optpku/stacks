/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RestrictedHom.Inverse
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Precomposition
public import ReasLib.CategoryTheory.Fibered.BasedCategory.ElementsMap
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Formal objects from presented prorepresentable functors

This module transports the evaluation equivalence for a restricted coyoneda functor across an
explicit prorepresentation.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject

open CompleteLocalAlgCat
open Functor.Fiber

noncomputable section

/-- Evaluation on identity truncations transported across a prorepresentation. -/
@[stacks 06HD]
def fromProrepresentableHom (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ restrictedCoyoneda R) :
    (BasedCategory.ofFunctor (CategoryOfElements.π U) ⥤ᵇ BasedCategory.ofFunctor p) ⥤
      Functor.Fiber (Functor.completion p) R :=
  BasedCategory.precomposition (BasedCategory.ofFunctor p)
      (CategoryOfElements.basedMap e.inv) ⋙ fromRestrictedHom p R

/-- Evaluation of a based morphism is obtained by precomposition with the prorepresentation. -/
theorem fromProrepresentableHom_obj (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ restrictedCoyoneda R)
    (φ : BasedCategory.ofFunctor (CategoryOfElements.π U) ⥤ᵇ BasedCategory.ofFunctor p) :
    (fromProrepresentableHom p e).obj φ =
      (fromRestrictedHom p R).obj
        (BasedFunctor.comp (CategoryOfElements.basedMap e.inv) φ) :=
  sorry

/-- The formal object obtained from a prorepresented morphism has base `R`. -/
theorem fromProrepresentableHom_base (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ restrictedCoyoneda R)
    (φ : BasedCategory.ofFunctor (CategoryOfElements.π U) ⥤ᵇ BasedCategory.ofFunctor p) :
    (fiberInclusion.obj ((fromProrepresentableHom p e).obj φ)).base = R :=
  sorry

/-- The evaluation equivalence remains an equivalence after transport across a prorepresentation. -/
instance fromProrepresentableHom_isEquivalence (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ restrictedCoyoneda R) :
    (fromProrepresentableHom p e).IsEquivalence := sorry

/-- The inverse comparison transports the nilpotency-pushforward construction across a
prorepresentation. -/
def toProrepresentableHom (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ restrictedCoyoneda R) :
    Functor.Fiber (Functor.completion p) R ⥤
      (BasedCategory.ofFunctor (CategoryOfElements.π U) ⥤ᵇ BasedCategory.ofFunctor p) :=
  toRestrictedHom (p := p) R ⋙
    BasedCategory.precomposition (BasedCategory.ofFunctor p)
      (CategoryOfElements.basedMap e.hom)

/-- The transported evaluation agrees with restricted evaluation for the canonical
prorepresentation. -/
theorem fromProrepresentableHom_refl (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k) :
    fromProrepresentableHom p (Iso.refl (restrictedCoyoneda R)) = fromRestrictedHom p R :=
  sorry

end

end FormalObject

