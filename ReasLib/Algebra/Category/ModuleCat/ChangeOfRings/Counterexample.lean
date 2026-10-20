module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Injective
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction-of-Scalars Counterexamples

Concrete non-flat ring maps witnessing that restriction of scalars need not preserve injective
objects.
-/

@[expose] public section

open CategoryTheory

namespace ModuleCat.RestrictScalars

/-- Remark 12.29.2 (5) [03B8]: for a prime `p`, restriction of scalars along
`ℤ → ZMod p` does not preserve injective objects. -/
@[stacks 03B8]
theorem intToZMod_not_preservesInjectiveObjects
    (p : ℕ) [Fact p.Prime] :
    ¬ (ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).PreservesInjectiveObjects := sorry

end ModuleCat.RestrictScalars
