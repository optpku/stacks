/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule

@[expose] public section

universe u v

namespace Submodule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Every submodule of a localized module over the localized ring is the localization
of a submodule over the original ring. -/
theorem exists_localized_eq (S : Submonoid R)
    (N : Submodule (Localization S) (LocalizedModule S M)) :
    ∃ N' : Submodule R M,
      N = N'.localized' (Localization S) S (LocalizedModule.mkLinearMap S M) := sorry

end Submodule
