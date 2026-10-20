module

public import ReasLib.RingTheory.Regular.RingMap
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Composition of regular ring maps

@stack 0H7S
@stack 07QI
-/

namespace RingHom.Regular

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable {f : A →+* B} {g : B →+* C}

/-- Lemma 15.42.3 (0H7S): a regular map with regular source and Noetherian target has regular
target. -/
@[stacks 0H7S "regularity ascends along a regular ring map"]
theorem isRegularRing [Algebra A B] (h : (algebraMap A B).Regular)
    [IsRegularRing A] [IsNoetherianRing B] : IsRegularRing B := sorry

/-- Lemma 15.41.4: regular maps compose when the fibers of the composite are Noetherian. -/
@[stacks 07QI "composition of regular ring maps"]
theorem comp_of_noetherianFibers (hf : f.Regular) (hg : g.Regular)
    (hfiber : ∀ p : PrimeSpectrum A,
      IsNoetherianRing ((g.comp f).Fiber p.asIdeal)) :
    (g.comp f).Regular := sorry

/-- Regular maps between Noetherian rings are closed under composition. -/
@[stacks 07QI "composition with a Noetherian target"]
theorem comp (hf : f.Regular) (hg : g.Regular) [IsNoetherianRing C] :
    (g.comp f).Regular := sorry

end RingHom.Regular
