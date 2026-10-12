/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Functors

/-!
# Naturality of graded-piece complexes

This leaf is the cochain-complex facade for the identity and composition laws of the associated
graded and graded-piece functors.  The shape-independent maps remain owned by
`HomologicalComplex.Filtered`; cochain-complex users can use these short declarations without
reconstructing the `ComplexShape.up ℤ` specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [HasCokernels A]

/-- The associated-graded map of the identity filtered cochain-complex morphism. -/
@[simp, stacks 012C "identity map of an associated-graded cochain complex"]
theorem associatedGradedMap_id (K : FilteredComplex A) :
    associatedGradedMap (𝟙 K) = 𝟙 K.associatedGraded := sorry

/-- Associated-graded maps of filtered cochain complexes preserve composition. -/
@[simp, stacks 012C "composition of associated-graded cochain-complex maps"]
theorem associatedGradedMap_comp {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M) :
    associatedGradedMap (f ≫ g) = associatedGradedMap f ≫ associatedGradedMap g := sorry

/-- The `p`-th graded-piece map of the identity filtered cochain-complex morphism. -/
@[simp, stacks 012C "identity map of a graded-piece cochain complex"]
theorem gradedPieceMap_id (K : FilteredComplex A) (p : ℤ) :
    gradedPieceMap (𝟙 K) p = 𝟙 (K.gradedPiece p) := sorry

/-- Maps on a fixed graded-piece cochain complex preserve composition. -/
@[simp, stacks 012C "composition of graded-piece cochain-complex maps"]
theorem gradedPieceMap_comp {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M) (p : ℤ) :
    gradedPieceMap (f ≫ g) p = gradedPieceMap f p ≫ gradedPieceMap g p := sorry

end CategoryTheory.FilteredComplex

end
