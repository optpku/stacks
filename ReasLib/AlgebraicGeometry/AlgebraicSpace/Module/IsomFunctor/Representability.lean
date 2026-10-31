/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IsomFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a finite-presentation morphism of algebraic spaces, the Isom functor
between finitely presented quasi-coherent modules that are flat over the base
and have proper support is represented by an algebraic space affine of finite
presentation over the base. -/
@[stacks 08K9]
theorem isomFunctor_isAffineFinitePresentationOver
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F.IsFinitePresentation] [G.IsFinitePresentation]
    (hF_flat : flatOver F f) (hG_flat : flatOver G f)
    (hF_support : ClosedSubset.ProperOver f (closedSupport F))
    (hG_support : ClosedSubset.ProperOver f (closedSupport G)) :
    IsAffineFinitePresentationOver (isomFunctor f F G) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
