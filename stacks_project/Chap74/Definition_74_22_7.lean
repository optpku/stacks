/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_22_6_Pullback
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u v

variable {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}

/- Definition 74.22.7: with `S`, `X`, `X'`, `Y`, `Y'`, `f`, `a`, `a'`, `h` as in Lemma 74.22.6,
the functor sending `(V, φ)` to `f^*(V, φ)` is the pullback functor on descent data. -/
@[stacks 0ADM] #check (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor :
  (a : Y ⟶ X) → (a' : Y' ⟶ X') → (h : X' ⟶ X) →
    (f : Y' ⟶ Y) → CommSq f a' a h →
      AlgebraicGeometry.AlgebraicSpace.DescentData (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a) ⥤
        AlgebraicGeometry.AlgebraicSpace.DescentData (fun _ : PUnit.{v + 1} ↦ Y') (fun _ ↦ a'))
