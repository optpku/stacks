/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a finite morphism of finite presentation between algebraic spaces over a scheme,
a quasi-coherent module is of finite presentation if and only if its pushforward is of
finite presentation. -/
@[stacks 0610]
theorem isFinitePresentation_iff_pushforward_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] [FinitePresentation f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ℱ.IsFinitePresentation ↔ ((pushforward f).obj ℱ).IsFinitePresentation :=
  sorry

/-- Pushforward along a finite morphism of finite presentation preserves finite
presentation of a quasi-coherent module on an algebraic space. -/
instance pushforward_obj_isFinitePresentation_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] [FinitePresentation f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFinitePresentation] :
    ((pushforward f).obj ℱ).IsFinitePresentation :=
  (isFinitePresentation_iff_pushforward_of_isFinite f ℱ).mp inferInstance

end AlgebraicGeometry.AlgebraicSpace.Modules
