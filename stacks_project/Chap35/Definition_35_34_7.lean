/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback
import StacksCheckRecall

open CategoryTheory

open AlgebraicGeometry

universe u

variable {X X' S S' : Scheme.{u}}

/- Definition 35.34.7: with the scheme morphisms and commutative square from Lemma 35.34.6,
the functor sending `(V, φ)` to its pullback `f^*(V, φ)` is the pullback functor on descent data. -/
@[stacks 02VR] #check (AlgebraicGeometry.Scheme.DescentData.Pullback.functor :
  (a : X ⟶ S) → (a' : X' ⟶ S') → (h : S' ⟶ S) →
    (f : X' ⟶ X) → CommSq f a' a h →
      Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a) ⥤
        Scheme.DescentData (fun _ : PUnit.{1} ↦ X') (fun _ : PUnit.{1} ↦ a'))
