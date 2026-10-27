/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.SmoothH0
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.SmoothH0.Genus
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 109.16.4 (1): we denote ℳ and name it the moduli stack of
smooth proper curves the algebraic stack 𝒞urves^{smooth, h0} parametrizing
families of curves introduced in Lemma 109.16.3. -/
@[stacks 0E82] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothH0 :
  (S : AlgebraicGeometry.Scheme.{u}) →
    CategoryTheory.ObjectProperty (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.Obj S))

/- Definition 109.16.4 (2): for g ≥ 0 we denote ℳ_g and name it the moduli
stack of smooth proper curves of genus g the algebraic stack introduced in
Lemma 109.16.5. -/
@[stacks 0E82] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothH0OfGenus :
  ℕ → (S : AlgebraicGeometry.Scheme.{u}) →
    CategoryTheory.ObjectProperty (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.Obj S))
