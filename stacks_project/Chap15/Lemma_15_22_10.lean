module

public import ReasLib.Algebra.Module.Torsion.Flatness
import StacksCheckRecall

/-!
# Lemma 15.22.10

@stack 0539
-/

universe u v

/- Lemma 15.22.10 (0539): over a valuation ring, an `A`-module is flat exactly when it is
torsion-free. The owner records the stronger Bezout-domain criterion. -/
@[stacks 0539]
#check fun {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {M : Type v} [AddCommGroup M] [Module A M] ↦
  (Module.Flat.iff_isTorsionFree_of_isBezout (R := A) (M := M) :
    Module.Flat A M ↔ Module.IsTorsionFree A M)
