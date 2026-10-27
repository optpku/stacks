/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus

/-!
# Base change of relative associated points of modules on algebraic spaces

For a locally-of-finite-type morphism, relative associated points of a
quasi-coherent module descend under cartesian base change and lift above every
compatible point of the changed base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
variable {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}

namespace relativeAssassin

/-- In a cartesian square of algebraic spaces whose original morphism is
locally of finite type, the relative assassin of the pullback of a
quasi-coherent module is contained in the preimage of its relative assassin. -/
@[stacks 0CV2]
theorem subset_preimage [AlgebraicSpace.LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g) :
    relativeAssassin f' ((pullback g').obj F) ⊆
      Points.map g' ⁻¹' relativeAssassin f F :=
  sorry

/-- If a point of `X'` is relatively associated to the pullback of a
quasi-coherent module in a cartesian square with locally-of-finite-type
original morphism, then its image in `X` is relatively associated. -/
theorem mem_map_of_mem [AlgebraicSpace.LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g)
    {x' : Points X'} (hx' : x' ∈ relativeAssassin f' ((pullback g').obj F)) :
    Points.map g' x' ∈ relativeAssassin f F :=
  sorry

/-- In a cartesian square of algebraic spaces with locally-of-finite-type
original morphism, every point relatively associated to a quasi-coherent
module lifts to a point relatively associated to its pullback above each
compatible point of the changed base. -/
@[stacks 0CV2]
theorem exists_of_mem_map_eq [AlgebraicSpace.LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g)
    {x : Points X} {y' : Points Y'} (hx : x ∈ relativeAssassin f F)
    (hxy : Points.map f x = Points.map g y') :
    ∃ x' : Points X',
      x' ∈ relativeAssassin f' ((pullback g').obj F) ∧
        Points.map g' x' = x ∧ Points.map f' x' = y' :=
  sorry

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
