/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport.Sheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 99.8.3: morphisms from the fppf sheaf of points of an algebraic space
`T` to `Quot_{F/X/B}` correspond to pairs `(h, F_T ⟶ Q)`, identified by kernels,
where `h : T ⟶ B` and `Q` is quasi-coherent, finitely presented, flat over `T`,
and has support proper over `T`. -/
@[stacks 0D3V] #check (AlgebraicGeometry.AlgebraicSpace.Quot.quotSheafHom_bijective :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] (T : AlgebraicSpace S),
    Function.Bijective (AlgebraicGeometry.AlgebraicSpace.Quot.toQuotSheafHom f F T))
