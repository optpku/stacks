module

public import ReasLib.LinearAlgebra.TensorProduct.Pi.FinitePresentation
public import ReasLib.RingTheory.Flatness.MittagLeffler.TensorProduct

/-!
# Finite Mittag-Leffler modules

For a finite module, the Mittag-Leffler condition supplies exactly the injectivity half missing
from the tensor-product characterization of finite presentation.
-/

@[expose] public section

universe u v

namespace Module.Finite

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- For a finite module, being Mittag-Leffler is equivalent to being finitely presented. -/
@[stacks 059R "finite criterion"]
theorem mittagLeffler_iff_finitePresentation [Module.Finite R M] :
    Module.MittagLeffler R M ↔ Module.FinitePresentation R M := sorry

end Module.Finite
