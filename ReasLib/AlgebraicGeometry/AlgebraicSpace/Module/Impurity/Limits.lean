/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Impurity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor

/-!
# Descent of impurities along directed affine limits

An impurity of a finite-type quasi-coherent module over a directed inverse limit of
affine schemes over `Y` descends to an impurity at some finite stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IsImpurity

/-- An impurity over a directed inverse limit of affine schemes descends to an
impurity at some stage through the canonical projection maps. -/
theorem exists_stage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Decent f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ SchemeOver Y)
    (hAff : ∀ i, IsAffine (D.obj i).left.left) (c : Cone D) (hc : IsLimit c)
    (t' t : c.pt.left.left) (ξ : Points (Limits.pullback f c.pt.hom))
    (h : IsImpurity f F y c.pt t' t ξ) :
    ∃ i, IsImpurity f F y (D.obj i) ((c.π.app i).left.left t')
      ((c.π.app i).left.left t) (Points.map (baseChangeSpaceMap f (c.π.app i)) ξ) :=
  sorry

end IsImpurity
end AlgebraicGeometry.AlgebraicSpace.Modules
