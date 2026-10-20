/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.FormalFunctions.Stalk
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {X Y : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/- Lemma 30.20.7: given a proper morphism `f : X ⟶ Y` with `Y` locally Noetherian
and a coherent sheaf `F` on `X`, for every point `y` of `Y` and every `p`,
the `m_y`-adic completion of the stalk `(R^p f_* F)_y` is isomorphic to
`lim_n H^p(X_n, F_n)` as `𝒪_{Y,y}^∧`-modules, where
`X_n = Spec(𝒪_{Y,y} ⧸ m_y^n) ×_Y X` is the infinitesimal neighbourhood of the
fibre `X_1 = X_y` and `F_n = i_n^* F`. Internally `scheme f y n` is the source's
`X_{n+1}`, so `n = 0` recovers `X_y`. -/
@[stacks 02OD] #check
  (AlgebraicGeometry.Scheme.Hom.FiberNeighbourhood.isIso_limitComparison :
    ∀ [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
      (F : X.Modules) [F.IsCoherent] (y : Y) (p : ℕ),
      IsIso (AlgebraicGeometry.Scheme.Hom.FiberNeighbourhood.limitComparison f F y p))
