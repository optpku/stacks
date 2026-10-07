module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Monoidal
public import ReasLib.Algebra.Homology.DifferentialGradedModule.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison with monoidal K-flatness for differential graded modules

The universe-polymorphic ground-ring predicate is the primary API.  This compatibility leaf
identifies it with monoidal K-flatness of the underlying complex when all carriers live in the
base-ring universe.
@stack 06XZ
-/

@[expose] public section

universe u w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R}

/-- For a differential graded module in the base-ring universe, K-flatness over the ground ring
agrees with monoidal K-flatness of its underlying cochain complex. -/
@[stacks 06XZ "comparison with monoidal K-flatness for differential graded modules"]
theorem isKFlat_iff_monoidal (M : DifferentialGradedModule.{u, u} A) :
    M.IsKFlat ↔ M.toCochainComplex.IsKFlat := sorry

end DifferentialGradedModule
