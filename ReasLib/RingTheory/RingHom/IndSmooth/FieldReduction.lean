module

public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.RingTheory.Regular.RingMap
public import ReasLib.RingTheory.RingHom.IndSmooth.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reduction of ind-smoothness to field sources

The field-case hypothesis is phrased for arbitrary ring homomorphisms out of a
field.  This removes the incidental choice of an `Algebra` instance and makes
the reduction reusable for maps obtained by base change or localization.
-/

@[expose] public section

universe u v u' v'

namespace RingHom.IndSmooth

/-- Lemma 16.8.4 (tag `07F5`): ind-smoothness for regular maps of Noetherian
commutative rings follows from the same property for all regular maps whose
source is a field. -/
@[stacks 07F5]
theorem of_field_cases
    {R : Type u} {Λ : Type v} [CommRing R] [CommRing Λ]
    (f : R →+* Λ) [IsNoetherianRing R] [IsNoetherianRing Λ]
    [f.Regular]
    (hfield :
      ∀ {K : Type u'} {B : Type v'} [Field K] [CommRing B]
        [IsNoetherianRing B] (g : K →+* B) [g.Regular],
        g.IndSmooth) :
    f.IndSmooth := sorry

end RingHom.IndSmooth
