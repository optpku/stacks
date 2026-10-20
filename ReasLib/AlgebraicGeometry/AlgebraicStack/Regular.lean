module

public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Regular.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothLocal

/-!
# Regular algebraic stacks

An algebraic stack is regular when it admits a surjective smooth atlas from a
regular scheme, in the sense of the smooth-local scheme property `Scheme.Regular`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is regular if it admits a surjective smooth atlas from a
regular scheme. -/
@[mk_iff]
class IsRegular {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- There is a surjective smooth 1-morphism from the slice of a regular
  scheme. -/
  exists_regular_smooth_cover :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ Scheme.Regular U.left

namespace IsRegular

/-- A regular algebraic stack admits a surjective smooth atlas from a regular
scheme. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsRegular X] :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        Scheme.Regular U.left :=
  sorry

/-- A surjective smooth atlas from a regular scheme witnesses that the algebraic
stack is regular. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [Scheme.Regular U.left] :
    IsRegular X :=
  sorry

/-- An algebraic stack is regular if and only if it admits a surjective smooth
atlas from a regular scheme. -/
theorem iff {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsRegular X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          Scheme.Regular U.left :=
  sorry

end IsRegular

/-- The canonical slice of a regular scheme over `S` is a regular algebraic
stack. -/
instance instIsRegular_slice {S : Scheme.{u}} (U : Over S)
    [Scheme.Regular U.left] :
    IsRegular (GroupoidsOver.slice U) where
  exists_regular_smooth_cover :=
    ⟨U, 𝟙 (GroupoidsOver.slice U), inferInstance, inferInstance, inferInstance⟩

/-- An algebraic stack is regular if and only if it admits a surjective smooth
scheme atlas whose source is regular. -/
theorem isRegular_iff_existsSurjectiveSmooth {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsRegular X ↔
      existsSurjectiveSmooth (Scheme.Regular : ObjectProperty Scheme.{u}) X :=
  sorry

/-- An algebraic stack is regular if and only if it has the smooth-local scheme
property `Scheme.Regular`. -/
theorem isRegular_iff_hasSmoothLocal {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsRegular X ↔
      hasSmoothLocal (Scheme.Regular : ObjectProperty Scheme.{u}) X :=
  sorry

end AlgebraicGeometry.AlgebraicStack

