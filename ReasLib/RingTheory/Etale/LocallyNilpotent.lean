module

public import ReasLib.RingTheory.Etale.Category
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale algebras over locally nilpotent quotients

Reduction modulo a locally nilpotent ideal is an equivalence on the category of etale algebras.

@stack 0ALI
-/

@[expose] public section

open CategoryTheory

universe u

namespace CommAlgCat.Etale

/-- Reduction modulo a locally nilpotent ideal is an equivalence on etale algebras.

The locally nilpotent proof is explicit rather than an instance because it is selected evidence
for the ideal and is not determined by the reduction functor's type. -/
@[stacks 0ALI "etale equivalence over a locally nilpotent quotient"]
theorem reduction_isEquivalence_of_isLocallyNilpotent
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.IsLocallyNilpotent) :
    Functor.IsEquivalence (reduction I) := sorry

end CommAlgCat.Etale
