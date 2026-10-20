module

public import ReasLib.Algebra.Homology.LocalCohomology.Derivation
import StacksCheckRecall

@[expose] public section

universe u

namespace Ideal.LocalCohomology

variable {A : Type u} [CommRing A]

/- Lemma 51.19.1: if `I` is finitely generated and represents the closed subset
`Z = V(I)`, every absolute derivation `θ` induces an additive operator on each
local cohomology module with support in `Z` satisfying the Leibniz rule along `θ`. -/
@[stacks 0EC5]
#check (Ideal.LocalCohomology.existsDerivationOperator :
  ∀ (I : Ideal A) (hI : I.FG) (θ : Derivation ℤ A A) (i : ℕ),
    ∃ D : Module.End ℤ ((localCohomology I i).obj (ModuleCat.of A A)),
      D.IsModuleDerivation θ)

end Ideal.LocalCohomology
