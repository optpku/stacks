/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor
public import ReasLib.CategoryTheory.ObjectProperty.Cover

/-!
# Effaceable Functors and Universal Delta Functors

This file separates the objectwise effaceability property of an ordinary functor from its main
application: a cohomological delta functor whose positive-degree functors are effaceable is
universal.
-/

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory

open Limits

namespace Functor

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B]

/-- A functor is effaceable when every source object admits a monomorphism on which the functor
acts by the zero morphism. -/
def IsEffaceable (F : A ⥤ B) : Prop :=
  ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ F.map u = 0

namespace IsEffaceable

/-- A functor is effaceable if it vanishes on an object property into which every object admits
a monomorphic embedding. -/
theorem of_vanishesOn {F : A ⥤ B} {P : ObjectProperty A} [P.HasMonoEmbedding]
    (hP : ∀ ⦃Y : A⦄, P Y → IsZero (F.obj Y)) :
    F.IsEffaceable := sorry

/-- Naturally isomorphic functors are simultaneously effaceable. -/
theorem iff_of_iso {F G : A ⥤ B} (e : F ≅ G) :
    F.IsEffaceable ↔ G.IsEffaceable := sorry

end IsEffaceable

end Functor

namespace CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

/-- A cohomological delta functor is universal when each of its positive-degree functors is
effaceable. -/
@[stacks 010T]
theorem isUniversal_of_effaceable (F : CohomologicalDeltaFunctor A B)
    (hF : ∀ n : ℕ, n > 0 → (F.F n).obj.IsEffaceable) :
    F.IsUniversal := sorry

end CohomologicalDeltaFunctor

end CategoryTheory
