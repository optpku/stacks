module

public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.GradedObject.Homology
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Filtered quasi-isomorphisms

A morphism of cochain complexes in `Fil(A)` is a filtered quasi-isomorphism when each associated
graded piece is a quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A morphism of filtered cochain complexes is a filtered quasi-isomorphism when every induced
map of graded-piece complexes is a quasi-isomorphism. -/
class IsFilteredQuasiIso {K L : FilteredComplex A} (f : K ⟶ L) : Prop where
  /-- Each associated-graded piece of a filtered quasi-isomorphism is a quasi-isomorphism. -/
  gradedPiece (p : ℤ) : QuasiIso (gradedPieceMap f p)

attribute [instance] IsFilteredQuasiIso.gradedPiece

/-- Filtered quasi-isomorphisms are exactly the morphisms whose graded-piece maps are
quasi-isomorphisms. -/
theorem isFilteredQuasiIso_iff {K L : FilteredComplex A} (f : K ⟶ L) :
    IsFilteredQuasiIso f ↔ ∀ p, QuasiIso (gradedPieceMap f p) := sorry

namespace IsFilteredQuasiIso

/-- The identity morphism of a filtered cochain complex is a filtered quasi-isomorphism. -/
instance id (K : FilteredComplex A) : IsFilteredQuasiIso (𝟙 K) := sorry

/-- Every isomorphism of filtered cochain complexes is a filtered quasi-isomorphism. -/
instance ofIsIso {K L : FilteredComplex A} (f : K ⟶ L) [IsIso f] :
    IsFilteredQuasiIso f := sorry

/-- A morphism of filtered cochain complexes is a filtered quasi-isomorphism if and only if the
induced map of associated graded complexes is a quasi-isomorphism. -/
theorem associatedGraded_iff {K L : FilteredComplex A} (f : K ⟶ L) :
    IsFilteredQuasiIso f ↔ QuasiIso (associatedGradedMap f) := sorry

end IsFilteredQuasiIso

/-- The morphism property of filtered quasi-isomorphisms on cochain complexes in `Fil(A)`. -/
def quasiIso (A : Type u) [Category.{v} A] [Abelian A] :
    MorphismProperty (FilteredComplex A) :=
  fun _ _ f ↦ IsFilteredQuasiIso f

/-- Membership in `FilteredComplex.quasiIso` is the filtered quasi-isomorphism class. -/
theorem mem_quasiIso_iff {K L : FilteredComplex A} (f : K ⟶ L) :
    quasiIso A f ↔ IsFilteredQuasiIso f := sorry

end CategoryTheory.FilteredComplex
