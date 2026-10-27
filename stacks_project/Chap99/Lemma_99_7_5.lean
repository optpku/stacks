/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Sheaf
import StacksCheckRecall

/-!
# Lemma 99.7.5

In Situation 99.7.1, morphisms of fppf sheaves from an algebraic space `T` over
`S` into `Q_{F/X/B}` (resp. `Q^{fp}_{F/X/B}`) are identified with pairs
`(h, F_T ⟶ Q)` where `h : T ⟶ B` and `Q` is quasi-coherent and flat over `T`
(resp. of finite presentation and flat over `T`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 99.7.5. Morphisms to the quotient sheaf correspond to kernel-identified
quasi-coherent quotient pairs flat over the algebraic-space base. -/
@[stacks 0D3U] #check (AlgebraicGeometry.AlgebraicSpace.Quot.sheafHom_bijective :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent] (T : AlgebraicSpace S),
    Function.Bijective (AlgebraicGeometry.AlgebraicSpace.Quot.toSheafHom f F T))

#check (AlgebraicGeometry.AlgebraicSpace.Quot.fpSheafHom_bijective :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent] (T : AlgebraicSpace S),
    Function.Bijective (AlgebraicGeometry.AlgebraicSpace.Quot.toFpSheafHom f F T))
