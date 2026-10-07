module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration.Naturality
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Preadditive
public import ReasLib.CategoryTheory.Homology.PageTower.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of Spectral-Sequence Page Filtrations

The cycle and boundary stages of a fixed graded entry are additive functors of the ambient
spectral sequence.  This leaf keeps those instances separate from the page-filtration owner and
from its naturality statements, so clients can opt into additive transport without importing
unrelated tower APIs.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory
namespace SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} {c : ℤ → ComplexShape κ}

namespace Cycle

/-- The fixed cycle-stage functor preserves addition of spectral-sequence morphisms. -/
@[stacks 011O "additivity of spectral-sequence cycle stages"]
noncomputable instance functor_additive (pq : κ) (r : ℕ+) :
    (functor (C := C) (c := c) pq r).Additive := sorry

end Cycle

namespace Boundary

/-- The fixed boundary-stage functor preserves addition of spectral-sequence morphisms. -/
@[stacks 011O "additivity of spectral-sequence boundary stages"]
noncomputable instance functor_additive (pq : κ) (r : ℕ+) :
    (functor (C := C) (c := c) pq r).Additive := sorry

end Boundary

namespace HomologyTower

/-- The fixed-grading homology-page-tower functor preserves addition of spectral-sequence
morphisms. -/
@[stacks 011O "additivity of homology-page tower construction"]
noncomputable instance functor_additive (pq : κ) :
    (functor (C := C) (c := c) pq).Additive := sorry

end HomologyTower

end SpectralSequence
end CategoryTheory
