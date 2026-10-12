/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_7_10_Conormal
import StacksCheckRecall

/-!
# Conormal sequence of an immersion of algebraic spaces

An immersion of algebraic spaces over a base algebraic space has a canonical
right-exact sequence relating the conormal sheaf to relative differentials.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {B X Z : AlgebraicSpace S}
variable (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ B)

/- Lemma 76.7.10: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `i : Z ⟶ X` be an immersion of algebraic spaces over `B`. There is a
canonical exact sequence `C_{Z/X} ⟶ i^* Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0`, where the
first arrow is induced by `d_{X/B}` and the second arrow comes from
Lemma 76.7.6. -/
@[stacks 05ZA] #check (exact_and_epi i f :
  (complex i f).Exact ∧ Epi (comparison i f))

/- The first arrow is the `d_{X/B}`-induced map out of the coborder pullback of
`I / I²`. -/
@[stacks 05ZA] #check (map i f :
  (Modules.pullback (IsImmersion.liftCoborder i)).obj
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i))) ⟶
    (Modules.pullback i).obj (relativeDifferentials f))

/- The second arrow is the Lemma 76.7.6 comparison on relative differentials. -/
@[stacks 05ZA] #check (comparison i f :
  (Modules.pullback i).obj (relativeDifferentials f) ⟶ relativeDifferentials (i ≫ f))
