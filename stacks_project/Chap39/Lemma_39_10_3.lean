module

import Mathlib.AlgebraicGeometry.Pullbacks
public import stacks_project.Chap39.Definition_39_10_2_IsFree
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable (S : Scheme.{u}) (G : Grp (Over S)) (X : Mod (Over S) G.X)

/- Lemma 39.10.3: The action of `G` on `X` is free on every scheme of
generalized points over `S` if and only if its shear morphism
`(g, x) ↦ (g • x, x)` is a monomorphism. -/
@[stacks 07S2] #check
  (CategoryTheory.Mod.isFree_iff_mono_leftSMul X :
    Mod.IsFree X ↔
      Mono (ModObj.leftSMul G.X X.X))
