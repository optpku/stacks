module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
import Mathlib.Tactic.CrossRefAttribute

/-!
# Noncompact punctured affine spaces
-/

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.PuncturedAffineSpace

universe u

noncomputable section

variable (ι : Type u) [Infinite ι] (k : Type u) [CommRing k] [Nontrivial k]

/-- Punctured affine space with infinitely many coordinates is not compact. -/
@[stacks 01K8]
theorem puncturedOpen_not_isCompact :
    ¬ IsCompact ((puncturedOpen ι k : (affineSpace ι k).Opens) :
      Set (affineSpace ι k)) := sorry

/-- The punctured-open immersion with infinitely many coordinates is not quasi-compact. -/
@[stacks 01K8]
theorem puncturedOpen_not_quasiCompact :
    ¬ QuasiCompact (puncturedOpen ι k).ι := sorry

end
end AlgebraicGeometry.PuncturedAffineSpace
