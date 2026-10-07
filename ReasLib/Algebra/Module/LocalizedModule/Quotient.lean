module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of Module Quotients

This leaf records the generator formula for the canonical equivalence between
a localized quotient and the quotient of a localized module.

@stack 05N6
-/

@[expose] public section

universe u v

namespace Submodule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Tag `05N6`: the inverse localized-quotient equivalence sends the
localized class of `x` to the class of the localized element `x`. -/
@[simp, stacks 05N6 "localized quotient inverse generator"]
theorem localizedQuotientEquiv_symm_mk
    (S : Submonoid R) (K : Submodule R M) (x : M) :
    (localizedQuotientEquiv S K).symm
        (LocalizedModule.mkLinearMap S (M ⧸ K) (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M x) := sorry

end Submodule
