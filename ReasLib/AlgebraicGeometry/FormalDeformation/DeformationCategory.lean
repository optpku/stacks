/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger

/-!
# Deformation categories

A deformation category is a predeformation category satisfying the
Rim-Schlessinger condition.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- A deformation category is a predeformation category satisfying the
Rim-Schlessinger condition. -/
class IsDeformationCategory (p : F ⥤ ArtinianLocalAlgCat Λ k) : Prop
    extends IsPredeformationCategory p where
  [hasRimSchlessinger : HasRimSchlessinger p]

attribute [instance] IsDeformationCategory.hasRimSchlessinger

/-- The identity functor on `ArtinianLocalAlgCat Λ k` is a deformation category. -/
instance instIsDeformationCategoryId :
    IsDeformationCategory (𝟭 (ArtinianLocalAlgCat Λ k)) := sorry

/-- A functor is a deformation category iff it is a predeformation category and satisfies
the Rim-Schlessinger condition (RS). -/
theorem isDeformationCategory_iff (p : F ⥤ ArtinianLocalAlgCat Λ k) :
    IsDeformationCategory p ↔ IsPredeformationCategory p ∧ HasRimSchlessinger p := sorry

end CategoryTheory.Functor
