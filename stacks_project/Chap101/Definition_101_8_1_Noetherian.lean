/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Lemma_94_19_1_Localization
public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Noetherian algebraic stacks

An algebraic stack is locally Noetherian when it admits a surjective smooth atlas
from a locally Noetherian scheme. It is quasi-separated in the absolute sense of
tag 050D (8): after viewing over Spec ℤ by Construction A, the diagonal is
quasi-compact and quasi-separated as a morphism representable by algebraic spaces.
It is Noetherian when it is quasi-compact, quasi-separated, and locally Noetherian.
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
  exists_noetherian_smooth_cover :
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

end IsLocallyNoetherian

/-- The canonical slice of a locally Noetherian scheme over `S` is a locally
Noetherian algebraic stack. -/
instance instIsLocallyNoetherian_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian U.left] :
    IsLocallyNoetherian (GroupoidsOver.slice U) where
  exists_noetherian_smooth_cover :=
    ⟨U, 𝟙 (GroupoidsOver.slice U), inferInstance, inferInstance, inferInstance⟩

/-- View an algebraic stack over `S` as an algebraic stack over `Spec ℤ` by
Construction A along the unique morphism `S ⟶ Spec ℤ`. -/
def viewedOverSpecZ {S : Scheme.{u}} (X : GroupoidsOver S) :
    GroupoidsOver (Spec (.of (ULift.{u} ℤ))) :=
  viewedOver (specULiftZIsTerminal.from S) X

/-- The projection of `viewedOverSpecZ X` is `X.p` followed by `Over.map` of the
unique morphism `S ⟶ Spec ℤ`. -/
theorem viewedOverSpecZ_p {S : Scheme.{u}} (X : GroupoidsOver S) :
    (viewedOverSpecZ X).p = X.p ⋙ Over.map (specULiftZIsTerminal.from S) :=
  sorry

/-- An algebraic stack is quasi-separated if, after viewing over `Spec ℤ`, the
diagonal is quasi-compact and quasi-separated as a morphism representable by
algebraic spaces. -/
@[mk_iff]
class IsQuasiSeparated {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- The absolute diagonal is quasi-compact on every scheme-slice representing morphism. -/
  quasiCompact_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))
  /-- The absolute diagonal is quasi-separated on every scheme-slice representing morphism. -/
  quasiSeparated_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated (Spec (.of (ULift.{u} ℤ))))
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))

namespace IsQuasiSeparated

/-- A quasi-separated algebraic stack has quasi-compact and quasi-separated
absolute diagonal. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsQuasiSeparated X] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)) :=
  sorry

/-- Quasi-compactness and quasi-separatedness of the absolute diagonal witness
that an algebraic stack is quasi-separated. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)))
    (h_quasiSeparated :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))) :
    IsQuasiSeparated X := sorry

end IsQuasiSeparated

/-- The canonical slice of an absolutely quasi-separated scheme is a
quasi-separated algebraic stack. -/
instance instIsQuasiSeparated_slice {S : Scheme.{u}} (U : Over S)
    [QuasiSeparatedSpace U.left] :
    IsQuasiSeparated (GroupoidsOver.slice U) := sorry

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
