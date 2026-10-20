/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor.Representability

/-!
# Proposition 99.3.10

In Situation 99.3.1, if `f` is of finite presentation and `G` is a finitely
presented `𝒪_X`-module, flat over `B`, with support proper over `B`, then
`Hom(F, G)` is an algebraic space affine over `B`. If also `F` is of finite
presentation, then `Hom(F, G)` is of finite presentation over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Proposition 99.3.10 (1): The Hom functor is an algebraic space affine over the base. -/
@[stacks 08K6] #check (AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor_isAffineOver :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] [G.IsFinitePresentation]
    (hG_flat : flatOver G f)
    (hG_support : Proper ((ClosedSubspaceStructure.reduced (closedSupport G)).ι ≫ f)),
    IsAffineOver (homFunctor f F G))

/- Proposition 99.3.10 (2): If `F` is finitely presented, the Hom functor is of finite
presentation over the base. -/
@[stacks 08K6] #check (AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor_isFinitePresentationOver :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F.IsFinitePresentation] [G.IsFinitePresentation]
    (hG_flat : flatOver G f)
    (hG_support : Proper ((ClosedSubspaceStructure.reduced (closedSupport G)).ι ≫ f)),
    IsFinitePresentationOver (homFunctor f F G))
