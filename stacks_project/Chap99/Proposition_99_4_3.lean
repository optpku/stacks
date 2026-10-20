/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IsomFunctor.Representability

/-!
# Proposition 99.4.3

In Situation 99.3.1, if `f` is of finite presentation and `F` and `G` are
finitely presented `𝒪_X`-modules, flat over `B`, with support proper over `B`,
then the functor `Isom(F, G)` is an algebraic space affine of finite
presentation over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Proposition 99.4.3: In Situation 99.3.1, if `f` is of finite presentation
and `F` and `G` are finitely presented `𝒪_X`-modules, flat over `B`, with
support proper over `B`, then the functor `Isom(F, G)` is an algebraic space
affine of finite presentation over `B`. -/
@[stacks 08K9]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomFunctor_isAffineFinitePresentationOver :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F.IsFinitePresentation] [G.IsFinitePresentation]
    (hF_flat : flatOver F f) (hG_flat : flatOver G f)
    (hF_support : ClosedSubset.ProperOver f (closedSupport F))
    (hG_support : ClosedSubset.ProperOver f (closedSupport G)),
    IsAffineFinitePresentationOver (isomFunctor f F G))

end AlgebraicGeometry.AlgebraicSpace.Modules
