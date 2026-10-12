/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.NegStage
public import ReasLib.CategoryTheory.Filtration.Complex.StageSequence.IsIso

/-!
# Isomorphism transport for negative filtration stages

This support leaf specializes the generic stage-sequence isomorphism API to
the negative-index facade.  Both componentwise and bundled forms are
registered for direct use by truncation and tower constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.NegStage

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
variable {K L : FilteredComplex A}

/-- Every component of a negative-stage diagram map is an isomorphism when the
filtered-complex map is. -/
@[stacks 0D8Z]
noncomputable instance map_app_isIso (f : K ⟶ L) (n : ℕ) [IsIso f] :
    IsIso ((map f).app n) := sorry

/-- A map of filtered complexes induces an isomorphism of negative-stage diagrams
when the original map is an isomorphism. -/
@[stacks 0D8Z]
noncomputable instance map_isIso (f : K ⟶ L) [IsIso f] :
    IsIso (map f) := sorry

variable (f : K ⟶ L) [IsIso f]
#synth IsIso ((map f).app 0)
#synth IsIso (map f)

end CategoryTheory.FilteredComplex.NegStage
