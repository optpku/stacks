module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Topology.Sheaves.Flasque

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.tilde

/-- An injective module over a commutative ring can have a nonsurjective restriction
from global sections of its associated sheaf to sections over a basic open. -/
theorem exists_injective_basicOpen_restriction_not_surjective :
    ∃ (A : CommRingCat.{u}) (J : ModuleCat.{u} A) (f : A),
      Module.Injective A J ∧
        ¬ Function.Surjective
            ((tilde J).presheaf.map
              (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op) := sorry

/-- The associated sheaf of an injective module over a commutative ring need not be flasque. -/
theorem exists_injective_not_isFlasque :
    ∃ (A : CommRingCat.{u}) (J : ModuleCat.{u} A),
      Module.Injective A J ∧ ¬ TopCat.Presheaf.IsFlasque (tilde J).presheaf := sorry

end AlgebraicGeometry.tilde
