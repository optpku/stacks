/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_29_3_ReducedFiberLocus
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.29.3: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y' ⟶ Y` be morphisms
of algebraic spaces over `S`. Denote `f' : X' ⟶ Y'` the base change of `f` by `g`.
Then the locus in `|Y'|` of points whose fibre under `f'` is geometrically reduced
equals the inverse image under `Points.map g` of the corresponding locus in `|Y|`. -/
@[stacks 0E09] #check
  (AlgebraicGeometry.AlgebraicSpace.geometricallyReducedFiberLocus_baseChange :
    ∀ {S : Scheme.{u}} {X Y Y' X' : AlgebraicSpace S},
      (f : X ⟶ Y) → (g : Y' ⟶ Y) → (g' : X' ⟶ X) → (f' : X' ⟶ Y') →
        IsPullback g' f' f g →
          geometricallyReducedFiberLocus f' =
            Points.map g ⁻¹' geometricallyReducedFiberLocus f)
