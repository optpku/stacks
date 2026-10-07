module

public import Mathlib.AlgebraicGeometry.Noetherian
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_7_1_SmoothLocal

/-!
# Locally Noetherian algebraic stacks

An algebraic stack is locally Noetherian when it admits a surjective smooth
atlas from a locally Noetherian scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is locally Noetherian if it admits a surjective smooth
atlas from a locally Noetherian scheme. -/
@[mk_iff]
class IsLocallyNoetherian {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop where
  /-- There is a surjective smooth 1-morphism from the slice of a locally
  Noetherian scheme. -/
  exists_locallyNoetherian_smooth_cover :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.IsLocallyNoetherian U.left

namespace IsLocallyNoetherian

/-- A locally Noetherian algebraic stack admits a surjective smooth atlas from a
locally Noetherian scheme. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsLocallyNoetherian X] :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.IsLocallyNoetherian U.left :=
  sorry

/-- A surjective smooth atlas from a locally Noetherian scheme witnesses that
the algebraic stack is locally Noetherian. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p]
    [AlgebraicGeometry.IsLocallyNoetherian U.left] :
    IsLocallyNoetherian X :=
  sorry

/-- An algebraic stack is locally Noetherian if and only if it admits a
surjective smooth atlas from a locally Noetherian scheme. -/
theorem iff {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsLocallyNoetherian X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          AlgebraicGeometry.IsLocallyNoetherian U.left :=
  sorry

end IsLocallyNoetherian

/-- The canonical slice of a locally Noetherian scheme over `S` is a locally
Noetherian algebraic stack. -/
instance instIsLocallyNoetherian_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian U.left] :
    IsLocallyNoetherian (GroupoidsOver.slice U) where
  exists_locallyNoetherian_smooth_cover :=
    ⟨U, 𝟙 (GroupoidsOver.slice U), inferInstance, inferInstance, inferInstance⟩

/-- An algebraic stack is locally Noetherian if and only if it admits a
surjective smooth scheme atlas whose source is locally Noetherian. -/
theorem isLocallyNoetherian_iff_existsSurjectiveSmooth {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsLocallyNoetherian X ↔
      existsSurjectiveSmooth
        (AlgebraicGeometry.IsLocallyNoetherian : ObjectProperty Scheme.{u}) X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
