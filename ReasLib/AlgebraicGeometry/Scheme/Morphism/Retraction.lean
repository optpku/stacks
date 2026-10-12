/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Retractions of scheme morphisms over a base

This file records global and target-local retractions of scheme morphisms that are compatible
with a fixed morphism to a base scheme.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {Z X S : Scheme.{u}}

/-- A morphism `i : Z ⟶ X` has a retraction over `S` relative to `f : X ⟶ S` if some
`r : X ⟶ Z` retracts `i` and is compatible with the morphisms to `S`. -/
def HasRetractionOver (i : Z ⟶ X) (f : X ⟶ S) : Prop :=
  ∃ r : X ⟶ Z, i ≫ r = 𝟙 Z ∧ r ≫ i ≫ f = f

/-- A retraction over a base is equivalently a morphism satisfying the retraction and
base-compatibility equations. -/
theorem hasRetractionOver_iff (i : Z ⟶ X) (f : X ⟶ S) :
    HasRetractionOver i f ↔
      ∃ r : X ⟶ Z, i ≫ r = 𝟙 Z ∧ r ≫ i ≫ f = f :=
  Iff.rfl

/-- A morphism has target-locally defined retractions over a base if every source point maps
into a target-open subset on which the restricted morphism admits a compatible retraction. -/
def LocallyHasRetractionOver (i : Z ⟶ X) (f : X ⟶ S) : Prop :=
  ∀ z : Z, ∃ U : X.Opens, i.base z ∈ U ∧
    HasRetractionOver (i ∣_ U) (U.ι ≫ f)

/-- Target-local retractions over a base are equivalently retractions on target-open
neighborhoods of the images of all source points. -/
theorem locallyHasRetractionOver_iff (i : Z ⟶ X) (f : X ⟶ S) :
    LocallyHasRetractionOver i f ↔
      ∀ z : Z, ∃ U : X.Opens, i.base z ∈ U ∧
        HasRetractionOver (i ∣_ U) (U.ι ≫ f) :=
  Iff.rfl

end AlgebraicGeometry.Scheme.Hom
