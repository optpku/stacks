/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Target

/-!
# Target-indexed dimensions of fibres

This compatibility module re-exports and checks the shared target-indexed
fibre-dimension API.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

#check (AlgebraicGeometry.Scheme.Hom.fiberDimension :
  ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → Y → WithBot ℕ∞)

#check (AlgebraicGeometry.Scheme.Hom.fiberDimension_apply :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y),
    f.fiberDimension y = topologicalKrullDim (f.fiber y))

#check (AlgebraicGeometry.Scheme.Hom.fiberDimension_baseChange :
  ∀ {Y X Y' X' : Scheme.{u}} (f : X ⟶ Y) [FiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
    IsPullback g' f' f g → f'.fiberDimension = f.fiberDimension ∘ g)

end AlgebraicGeometry.Scheme.Hom
