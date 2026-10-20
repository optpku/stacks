module

public import ReasLib.CategoryTheory.Filtration.Complex.GradedPieceColumn

/-!
# Isomorphism transport for graded-piece columns

An isomorphism of filtered complexes induces isomorphisms on every fixed graded-piece column.
Both the component-level and bundled homological-complex-level instances are exposed here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]

namespace GradedPiece.Column

/-- Every component of a graded-piece column map is an isomorphism when the filtered map is. -/
@[stacks 012M "isomorphism on graded-piece column components"]
noncomputable instance map_f_isIso {K L : FilteredComplex C} (f : K ⟶ L) (p q : ℤ)
    [IsIso f] : IsIso ((map f p).f q) := sorry

/-- A graded-piece column map is an isomorphism when its filtered-complex map is. -/
@[stacks 012M "isomorphism of graded-piece column maps"]
noncomputable instance map_isIso {K L : FilteredComplex C} (f : K ⟶ L) (p : ℤ)
    [IsIso f] : IsIso (map f p) := sorry

variable {K L : FilteredComplex C} (f : K ⟶ L) [IsIso f]
#synth IsIso (map f 0)
#synth IsIso ((map f 0).f 0)

end GradedPiece.Column

end CategoryTheory.FilteredComplex
