/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompletionFunctoriality
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber

/-!
# Essential surjectivity of smooth morphisms

A smooth morphism of categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
that is essentially surjective on the residue fiber is essentially surjective,
as is its induced functor on formal objects.
-/

@[expose] public section

open CategoryTheory
open Functor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{v} F] [Category.{v} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
variable [IsFibered.InGroupoids p.op] [IsFibered.InGroupoids q.op]

namespace CategoryTheory.BasedFunctor

/-- A smooth morphism of categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
that is essentially surjective on the residue fiber is essentially surjective. -/
instance essSurj (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) [IsSmooth φ]
    [(φ.fiberFunctor (ArtinianLocalAlgCat.residue Λ k)).EssSurj] :
    φ.toFunctor.EssSurj := sorry

/-- The induced functor on formal objects of a smooth morphism of categories cofibered
in groupoids over `ArtinianLocalAlgCat Λ k` that is essentially surjective on the
residue fiber is essentially surjective. -/
instance map_essSurj (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    [IsSmooth φ] [(φ.fiberFunctor (ArtinianLocalAlgCat.residue Λ k)).EssSurj] :
    (FormalObject.map φ).EssSurj := sorry

end CategoryTheory.BasedFunctor
