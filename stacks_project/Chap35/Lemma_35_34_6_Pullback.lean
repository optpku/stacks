/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback

@[expose] public section

open CategoryTheory

open AlgebraicGeometry

universe u

variable {X X' S S' : Scheme.{u}}

#check (Scheme.DescentData.Pullback.functor :
  (a : X ⟶ S) → (a' : X' ⟶ S') → (h : S' ⟶ S) →
    (f : X' ⟶ X) → CommSq f a' a h →
      Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a) ⥤
        Scheme.DescentData (fun _ : PUnit.{1} ↦ X') (fun _ : PUnit.{1} ↦ a'))
