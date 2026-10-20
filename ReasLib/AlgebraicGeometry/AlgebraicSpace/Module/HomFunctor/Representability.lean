/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Over

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a locally finite type, quasi-separated morphism to a Noetherian algebraic space,
the Hom functor of finite-type quasi-coherent modules is represented by an algebraic space
affine and of finite presentation over the base when the target module is flat over the
base and has proper support over it. -/
theorem homFunctor_isAffineFinitePresentation
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F.IsFiniteType] [G.IsFiniteType] (hG_flat : flatOver G f)
    (hG_support : Proper ((ClosedSubspaceStructure.reduced (closedSupport G)).ι ≫ f)) :
    IsAffineFinitePresentationOver (homFunctor f F G) := sorry

/-- For a finite-presentation morphism of algebraic spaces, the Hom functor of
quasi-coherent modules is represented by an algebraic space affine over the base when
the target module is finitely presented, flat over the base, and has proper support. -/
theorem homFunctor_isAffineOver
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] [G.IsFinitePresentation]
    (hG_flat : flatOver G f)
    (hG_support : Proper ((ClosedSubspaceStructure.reduced (closedSupport G)).ι ≫ f)) :
    IsAffineOver (homFunctor f F G) := sorry

/-- For a finite-presentation morphism of algebraic spaces and finitely presented
quasi-coherent modules, the Hom functor is represented by an algebraic space of finite
presentation over the base when the target module is flat over the base and has
proper support. -/
theorem homFunctor_isFinitePresentationOver
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F.IsFinitePresentation] [G.IsFinitePresentation]
    (hG_flat : flatOver G f)
    (hG_support : Proper ((ClosedSubspaceStructure.reduced (closedSupport G)).ι ≫ f)) :
    IsFinitePresentationOver (homFunctor f F G) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
