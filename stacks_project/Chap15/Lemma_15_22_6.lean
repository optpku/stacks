module

public import ReasLib.Algebra.Module.Torsion.LocalCriterion
import StacksCheckRecall

/-!
# Lemma 15.22.6

@stack 0AUT
-/

universe u v

/- Lemma 15.22.6 (0AUT): an `R`-module over a domain is torsion-free exactly when every
localization at a maximal ideal is torsion-free. -/
@[stacks 0AUT]
#check fun {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] ↦
  (Module.IsTorsionFree.iff_atPrime_maximal (R := R) (M := M) :
    Module.IsTorsionFree R M ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        Module.IsTorsionFree (Localization.AtPrime m)
          (LocalizedModule.AtPrime m M))
