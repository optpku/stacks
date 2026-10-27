/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Fiberwise

/-!
# Flatness of morphisms of locally Noetherian algebraic spaces

Flatness of a composite and of all induced fibre morphisms imply flatness of the first
morphism. If the first morphism is also surjective, the second morphism is flat as well.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a triangle of locally Noetherian algebraic spaces over a scheme, flatness of the
composite and of every induced fibre morphism imply flatness of the first morphism. -/
@[stacks 0APS]
theorem Flat.of_fiberFlatOver_of_isLocallyNoetherian {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [Flat (f ≫ h)] (h_fiber : ∀ z : Points Z, fiberFlatOver f h z) : Flat f :=
  sorry

/-- For a triangle of locally Noetherian algebraic spaces over a scheme, if the composite
and every induced fibre morphism are flat and the first morphism is surjective, then the
second morphism is flat. -/
@[stacks 0APS]
theorem Flat.base_of_fiberFlatOver_of_surjective_of_isLocallyNoetherian
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [Flat (f ≫ h)] [Surjective f]
    (h_fiber : ∀ z : Points Z, fiberFlatOver f h z) : Flat h :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
