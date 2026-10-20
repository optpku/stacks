/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory

/-!
# Smooth morphisms of predeformation categories

A smooth morphism between predeformation categories is essentially surjective and identifies
absolute smoothness of its source and target.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type w} [Category.{v} F] [Category.{v} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.BasedFunctor

/-- A smooth morphism of predeformation categories over `ArtinianLocalAlgCat Λ k` is
essentially surjective. -/
instance essSurj_of_isPredeformationCategory [Functor.IsPredeformationCategory p]
    [Functor.IsPredeformationCategory q]
    (φ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p) [IsSmooth φ] :
    φ.toFunctor.EssSurj := sorry

/-- The structure morphism of a predeformation category is smooth if and only if its composite
with a smooth morphism from a predeformation category is smooth. -/
theorem isSmooth_toBase_iff_comp [Functor.IsPredeformationCategory p]
    [Functor.IsPredeformationCategory q]
    (φ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p) [IsSmooth φ] :
    IsSmooth (BasedCategory.toBase (BasedCategory.ofFunctor p)) ↔
      IsSmooth (φ ⋙ BasedCategory.toBase (BasedCategory.ofFunctor p)) := sorry

end CategoryTheory.BasedFunctor

namespace CategoryTheory.Functor

/-- A smooth morphism between predeformation categories identifies absolute smoothness of
its target and source. -/
@[stacks 06HQ]
theorem isSmooth_iff_of_smooth [IsPredeformationCategory p] [IsPredeformationCategory q]
    (φ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p) [BasedFunctor.IsSmooth φ] :
    IsSmooth p ↔ IsSmooth q := sorry

end CategoryTheory.Functor
