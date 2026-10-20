/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Curve.StableCurves
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry

/- Definition 109.22.4: we denote ℳ̄ and name it the moduli stack of
stable curves the algebraic stack 𝒞urves^{stable} parametrizing stable
families of curves introduced in Lemma 109.22.3. -/
@[stacks 0E77] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.stable :
  ∀ S : Scheme.{u},
    CategoryTheory.ObjectProperty (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.Obj S))

/- Definition 109.22.4 (2): for g ≥ 2 we denote ℳ̄_g and name it the moduli
stack of stable curves of genus g the algebraic stack introduced in
Lemma 109.22.5. -/
@[stacks 0E77] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.stableOfGenus :
  ℕ → ∀ S : Scheme.{u},
    CategoryTheory.ObjectProperty (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.Obj S))
