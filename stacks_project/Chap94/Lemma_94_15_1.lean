/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map

/-!
# Lifting smooth surjective scheme atlases along morphisms of algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 94.15.1: let `S` be a scheme contained in `Sch_fppf`. Let
`f : X ⟶ Y` be a 1-morphism of algebraic stacks over `S`. Let `V` be an object
of `(Sch/S)_fppf`, and let `y : GroupoidsOver.slice V ⟶ Y` be surjective and
smooth. Then there exist an object `U` of `(Sch/S)_fppf`, a morphism
`α : U ⟶ V`, and a 1-morphism `x : GroupoidsOver.slice U ⟶ X` such that the
square with `a := overMap α : GroupoidsOver.slice U ⟶ GroupoidsOver.slice V`
is 2-commutative, i.e. `Nonempty (x ≫ f ≅ a ≫ y)`, and such that `x` is
surjective and smooth. -/
@[stacks 04T1]
theorem exists_smoothSurjective_atlas_lift {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {V : Over S}
    (y : GroupoidsOver.slice V ⟶ Y) (hy_smooth : Groupoids.Hom.Smooth y)
    (hy_surj : Groupoids.Hom.Surjective y) :
    ∃ (U : Over S) (α : U ⟶ V) (x : GroupoidsOver.slice U ⟶ X),
      Nonempty (x ≫ f ≅ overMap α ≫ y) ∧
        Groupoids.Hom.Smooth x ∧ Groupoids.Hom.Surjective x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
