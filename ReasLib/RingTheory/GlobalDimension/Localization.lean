module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import ReasLib.RingTheory.GlobalDimension.Basic

@[expose] public section

/-!
# Localization and Global Dimension

The global-dimension bound of a ring descends to every localization. Consumers
can use either the explicit theorem or the canonical typeclass instance.
-/

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R]

namespace HasGlobalDimensionLE

/-- A localization preserves a uniform global-dimension bound. -/
@[stacks 00O8]
theorem localization (n : ℕ) (S : Submonoid R) [HasGlobalDimensionLE R n] :
    HasGlobalDimensionLE (Localization S) n := sorry

end HasGlobalDimensionLE

namespace IsFiniteGlobalDimensionRing

/-- Finite global dimension is preserved by localization. -/
@[stacks 00O8 "finite localization"]
theorem localization (S : Submonoid R) [IsFiniteGlobalDimensionRing R] :
    IsFiniteGlobalDimensionRing (Localization S) := sorry

end IsFiniteGlobalDimensionRing

/-- A localization of a ring of global dimension at most `n` again has global
dimension at most `n`. -/
@[stacks 00O8]
instance localization_hasGlobalDimensionLE
    (n : ℕ) (S : Submonoid R) [HasGlobalDimensionLE R n] :
    HasGlobalDimensionLE (Localization S) n := sorry

end
