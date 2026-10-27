/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.Impurity

/-!
# Flat ascent of impurities

Impurities of finite-type quasi-coherent modules ascend along morphisms of
pointed algebraic spaces that are flat at the selected point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace Impurity

/-- For a finite-type decent morphism of algebraic spaces and a finite-type
quasi-coherent module, an impurity above a point ascends along a pointed
morphism flat at its selected point. The new impurity scheme is étale over
the base change of the original impurity scheme. -/
@[stacks 0CVA]
theorem exists_of_flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    {Y1 : AlgebraicSpace S} (φ : Y1 ⟶ Y) {y1 : Points Y1}
    (h_map : Points.map φ y1 = y) (h_flat : FlatAt φ y1)
    (I : Impurity F f y) :
    ∃ (I1 : Impurity ((Modules.pullback (Limits.pullback.fst f φ)).obj F)
        (Limits.pullback.snd f φ) y1)
      (π : ofOver I1.T ⟶ Limits.pullback φ I.g),
      AlgebraicSpace.Etale π ∧ I1.g = π ≫ Limits.pullback.fst φ I.g :=
  sorry

end Impurity
end AlgebraicGeometry.AlgebraicSpace.Modules
