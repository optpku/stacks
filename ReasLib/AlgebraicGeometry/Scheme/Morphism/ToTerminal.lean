/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.CategoryTheory.MorphismProperty.ToTerminal

/-!
# Absolute scheme properties as terminal-morphism properties
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Remark 26.21.18 (1): the absolute form of `QuasiCompact` is compactness of the underlying
scheme. -/
@[stacks 0816, simp]
theorem quasiCompact_toTerminal_iff (X : Scheme.{u}) :
    MorphismProperty.toTerminal @QuasiCompact X ↔ CompactSpace X := sorry

/-- Remark 26.21.18 (2): the absolute form of `QuasiSeparated` is `QuasiSeparatedSpace`. -/
@[stacks 0816, simp]
theorem quasiSeparated_toTerminal_iff (X : Scheme.{u}) :
    MorphismProperty.toTerminal @QuasiSeparated X ↔ QuasiSeparatedSpace X := sorry

/-- Remark 26.21.18 (3): the absolute form of `IsSeparated` is `Scheme.IsSeparated`. -/
@[stacks 0816, simp]
theorem isSeparated_toTerminal_iff (X : Scheme.{u}) :
    MorphismProperty.toTerminal @IsSeparated X ↔ X.IsSeparated := sorry

/-- Quasi-separated morphisms have the postcomposition cancellation needed by the terminal-object
criterion. -/
@[stacks 0816 "quasi-separated postcomposition cancellation"]
instance quasiSeparated_hasOfPostcompProperty :
    MorphismProperty.HasOfPostcompProperty @QuasiSeparated @QuasiSeparated := sorry

/-- Separated morphisms have the postcomposition cancellation needed by the terminal-object
criterion. -/
@[stacks 0816 "separated postcomposition cancellation"]
instance isSeparated_hasOfPostcompProperty :
    MorphismProperty.HasOfPostcompProperty @IsSeparated @IsSeparated := sorry

/-- The conjunction of quasi-compactness and quasi-separatedness has postcomposition cancellation. -/
@[stacks 0816 "quasi-compact quasi-separated postcomposition cancellation"]
instance quasiCompact_inf_quasiSeparated_hasOfPostcompProperty :
    MorphismProperty.HasOfPostcompProperty
      (@QuasiCompact ⊓ @QuasiSeparated) (@QuasiCompact ⊓ @QuasiSeparated) := sorry

/-- The conjunction of quasi-compactness and separatedness has postcomposition cancellation. -/
@[stacks 0816 "quasi-compact separated postcomposition cancellation"]
instance quasiCompact_inf_isSeparated_hasOfPostcompProperty :
    MorphismProperty.HasOfPostcompProperty
      (@QuasiCompact ⊓ @IsSeparated) (@QuasiCompact ⊓ @IsSeparated) := sorry

end AlgebraicGeometry
