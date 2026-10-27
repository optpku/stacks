/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Fiberwise

/-!
# Fibrewise criteria for flat morphisms of algebraic spaces

Flatness in a triangle of algebraic spaces follows from flatness over the base and on
every fibre, under finite-presentation and finite-type hypotheses.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- In a triangle of algebraic spaces, if the source is locally of finite presentation and
flat over the base, the intermediate space is locally of finite type over the base, and
every source fibre is flat over the corresponding intermediate fibre, then the morphism
from the source to the intermediate space is flat. -/
theorem Flat.of_fiberFlatOver {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ h)]
    [Flat (f ≫ h)] [LocallyOfFiniteType h]
    (h_fiber : ∀ z : Points Z, fiberFlatOver f h z) : Flat f :=
  sorry

/-- In a triangle of algebraic spaces, if the source is locally of finite presentation and
flat over the base, the intermediate space is locally of finite type over the base, every
source fibre is flat over the corresponding intermediate fibre, and the morphism from the
source to the intermediate space is surjective, then the intermediate space is flat over
the base. -/
theorem Flat.base_of_fiberFlatOver_of_surjective {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ h)] [Flat (f ≫ h)] [LocallyOfFiniteType h]
    [Surjective f] (h_fiber : ∀ z : Points Z, fiberFlatOver f h z) : Flat h :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
