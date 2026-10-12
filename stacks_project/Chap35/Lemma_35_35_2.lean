/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Over
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 35.35.2: For a surjective flat morphism `h : S' ⟶ S`, the base change
functor `Over.pullback h : Over S ⥤ Over S'` is faithful. -/
@[stacks 02VX] #check
  (AlgebraicGeometry.Flat.instFaithfulOverPullbackOfSurjective :
    ∀ {S' S : Scheme.{u}} (h : S' ⟶ S) [Flat h] [Surjective h],
      (Over.pullback h).Faithful)
