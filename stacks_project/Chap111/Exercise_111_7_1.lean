module

public import ReasLib.Algebra.Module.LocalizedModule.Localization
public import Mathlib.RingTheory.Localization.Ideal
import StacksCheckRecall

@[expose] public section

universe u v

section

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Exercise 111.7.1: for a ring `A`, multiplicative `S ⊂ A`, `A`-module `M`, and
`S⁻¹A`-submodule `N ⊂ S⁻¹M`, there exists an `A`-submodule `N' ⊂ M` with `N = S⁻¹N'`.
Here `S⁻¹N'` is `N'.localized' (Localization S) S (LocalizedModule.mkLinearMap S M)`. -/
@[stacks 0767]
#check (Submodule.exists_localized_eq : ∀ (S : Submonoid R)
  (N : Submodule (Localization S) (LocalizedModule S M)),
  ∃ N' : Submodule R M,
    N = N'.localized' (Localization S) S (LocalizedModule.mkLinearMap S M))

/- Ideal specialization: the same result applies in particular to ideals of `S⁻¹A`, recovered as
the case `M = A`. Mathlib owns this as `IsLocalization.map_under`: every ideal `J` of
`Localization S` equals the extension of its contraction `J.under R`. -/
#check (IsLocalization.map_under S (Localization S) :
  ∀ J : Ideal (Localization S), Ideal.map (algebraMap R (Localization S)) (J.under R) = J)

end
