module

public import Mathlib.AlgebraicGeometry.Properties
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_7_1_SmoothLocal

/-!
# Reduced algebraic stacks

An algebraic stack is reduced when it admits a surjective smooth atlas from a
reduced scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is reduced if it admits a surjective smooth atlas from a
reduced scheme. -/
@[mk_iff]
class IsReduced {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- There is a surjective smooth 1-morphism from the slice of a reduced scheme. -/
  exists_reduced_smooth_cover :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.IsReduced U.left

namespace IsReduced

/-- A reduced algebraic stack admits a surjective smooth atlas from a reduced
scheme. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsReduced X] :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.IsReduced U.left :=
  sorry

/-- A surjective smooth atlas from a reduced scheme witnesses that the algebraic
stack is reduced. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicGeometry.IsReduced U.left] :
    IsReduced X :=
  sorry

/-- An algebraic stack is reduced if and only if it admits a surjective smooth
atlas from a reduced scheme. -/
theorem iff {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsReduced X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          AlgebraicGeometry.IsReduced U.left :=
  sorry

end IsReduced

/-- The canonical slice of a reduced scheme over `S` is a reduced algebraic
stack. -/
instance instIsReduced_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsReduced U.left] :
    IsReduced (GroupoidsOver.slice U) where
  exists_reduced_smooth_cover :=
    ⟨U, 𝟙 (GroupoidsOver.slice U), inferInstance, inferInstance, inferInstance⟩

/-- An algebraic stack is reduced if and only if it admits a surjective smooth
scheme atlas whose source is reduced. -/
theorem isReduced_iff_existsSurjectiveSmooth {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsReduced X ↔
      existsSurjectiveSmooth
        (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
