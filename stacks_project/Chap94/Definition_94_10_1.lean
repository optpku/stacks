/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

universe u

/- Definition 94.10.1: let `S` be a scheme, and let `f : X ⟶ Y` be a `1`-morphism
of categories fibred in groupoids over `(Sch/S)_fppf` that is representable by
algebraic spaces (`relativelyRepresentableByAlgebraicSpaces f`). Let `P` be a
property of morphisms of algebraic spaces that is stable under base change
(`P.IsStableUnderBaseChange`) and fppf local on the target
(`P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)`). Then `f` has property
`P` if for every `U` in `Ob((Sch/S)_fppf)` and any `y : GroupoidsOver.slice U ⟶ Y`
the representing morphism `fy : Fy ⟶ AlgebraicSpace.ofOver U` of diagram 94.9.1.1
(`RepresentsBaseChange f y Fy fy`) has property `P`. -/
@[stacks 03YK] #check
  (has : ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S},
    MorphismProperty (AlgebraicSpace S) → (X ⟶ Y) → Prop)
