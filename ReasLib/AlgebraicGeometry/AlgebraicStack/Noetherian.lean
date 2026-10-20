module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothLocal

/-!
# Noetherian algebraic stacks

An algebraic stack is locally Noetherian when it admits a surjective smooth atlas
from a locally Noetherian scheme. It is Noetherian when it is quasi-compact,
absolutely quasi-separated, and locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is locally Noetherian if it admits a surjective smooth atlas
from a locally Noetherian scheme. -/
@[mk_iff]
class IsLocallyNoetherian {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- There is a surjective smooth 1-morphism from the slice of a locally Noetherian scheme. -/
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
        AlgebraicGeometry.IsLocallyNoetherian U.left := sorry

/-- A surjective smooth atlas from a locally Noetherian scheme witnesses that the
algebraic stack is locally Noetherian. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicGeometry.IsLocallyNoetherian U.left] :
    IsLocallyNoetherian X := sorry

/-- An algebraic stack is locally Noetherian if and only if it admits a
surjective smooth atlas from a locally Noetherian scheme. -/
theorem iff {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsLocallyNoetherian X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          AlgebraicGeometry.IsLocallyNoetherian U.left :=
  isLocallyNoetherian_iff X

end IsLocallyNoetherian

/-- The canonical slice of a locally Noetherian scheme over `S` is a locally
Noetherian algebraic stack. -/
instance instIsLocallyNoetherian_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian U.left] :
    IsLocallyNoetherian (GroupoidsOver.slice U) where
  exists_locallyNoetherian_smooth_cover :=
    ⟨U, 𝟙 (GroupoidsOver.slice U), inferInstance, inferInstance, inferInstance⟩

/-- The slice associated to a morphism from a locally Noetherian scheme is a
locally Noetherian algebraic stack. -/
instance instIsLocallyNoetherian_slice_mk {S T : Scheme.{u}} (f : T ⟶ S)
    [AlgebraicGeometry.IsLocallyNoetherian T] :
    IsLocallyNoetherian (GroupoidsOver.slice (Over.mk f)) :=
  @instIsLocallyNoetherian_slice S (Over.mk f)
    (inferInstanceAs (AlgebraicGeometry.IsLocallyNoetherian T))

/-- An algebraic stack is locally Noetherian if and only if it admits a
surjective smooth scheme atlas whose source is locally Noetherian. -/
theorem isLocallyNoetherian_iff_existsSurjectiveSmooth {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsLocallyNoetherian X ↔
      existsSurjectiveSmooth
        (AlgebraicGeometry.IsLocallyNoetherian : ObjectProperty Scheme.{u}) X := by
  constructor
  · intro h
    exact h.exists_locallyNoetherian_smooth_cover
  · intro h
    exact ⟨h⟩

/-- An algebraic stack is Noetherian if it is quasi-compact, quasi-separated, and
locally Noetherian. -/
@[mk_iff]
class IsNoetherian {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop extends
    IsQuasiCompact X, IsQuasiSeparated X, IsLocallyNoetherian X

namespace IsNoetherian

/-- A Noetherian algebraic stack is quasi-compact, quasi-separated, and locally
Noetherian. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsNoetherian X] :
    IsQuasiCompact X ∧ IsQuasiSeparated X ∧ IsLocallyNoetherian X := sorry

/-- Quasi-compactness, quasi-separatedness, and local Noetherianity together
witness that an algebraic stack is Noetherian. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsQuasiCompact X] [IsQuasiSeparated X] [IsLocallyNoetherian X] :
    IsNoetherian X := sorry

end IsNoetherian

/-- The canonical slice of a Noetherian scheme over `S` is a Noetherian algebraic
stack. -/
instance instIsNoetherian_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsNoetherian U.left] :
    IsNoetherian (GroupoidsOver.slice U) where
  toIsQuasiCompact := instIsQuasiCompact_slice U
  toIsQuasiSeparated := instIsQuasiSeparated_slice U
  toIsLocallyNoetherian := instIsLocallyNoetherian_slice U

end AlgebraicGeometry.AlgebraicStack
