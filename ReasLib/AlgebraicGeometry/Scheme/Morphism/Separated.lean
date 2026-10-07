module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic separatedness bridges for schemes
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Lemma 26.21.16: a scheme separated over a separated scheme is separated. -/
@[stacks 01KW "source separatedness"]
theorem Scheme.Hom.source_isSeparated
    (f : X ⟶ S) [IsSeparated f] [S.IsSeparated] : X.IsSeparated := sorry

end AlgebraicGeometry
