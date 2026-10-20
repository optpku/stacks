/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.RelativeFunctoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsolutePseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Naturality.Construction
public import ReasLib.CategoryTheory.Fibered.InSets.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Set-fibred relative inertia naturality construction

This leaf owns the canonical relative-to-absolute comparison for set-fibred pseudo-comma
arrows. Its projection and component readouts are layered separately.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Sets

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia

namespace toInertia

/-- Mapping relative inertia and then retaining the automorphism is naturally isomorphic to
first retaining the automorphism and then applying absolute inertia to the source-side functor. -/
@[stacks 04Z5 "set-fibred relative-to-absolute inertia naturality"]
def naturalityIso
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    RelativeInertia.map G G' comm ≫ toInertia F₂ ≅
      toInertia F₁ ≫ (Inertia.pseudofunctor C).map G :=
  Bicategory.InducedBicategory.isoMk
    (BasedCategory.RelativeInertia.toInertia.naturalityIso
      (FiberedCategoryOver.Sets.toBasedFunctor G)
      (FiberedCategoryOver.Sets.toBasedFunctor G')
      (Bicategory.InducedBicategory.Iso.toAmbient comm))

end toInertia

end RelativeInertia

end FiberedCategoryOver.Sets

end CategoryTheory
