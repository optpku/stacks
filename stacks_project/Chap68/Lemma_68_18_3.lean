/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_18_3_Fibre
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.18.3: In the cartesian square (68.18.0.1) of algebraic spaces over a
scheme `S`, if `hZ : Z' ⟶ Z` is a morphism and `z' ∈ |Z'|` maps to `z`, then the
induced map `F_{x, z'} → F_{x, z}` is surjective. Here `W' = X ×_Y Z' = W ×_Z Z'`,
and the map is the restriction of `|W'| → |W|`. -/
@[stacks 0AC5] #check Points.fibreMap_surjective
