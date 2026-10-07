module

public import Mathlib.RingTheory.RingHom.Etale
public import ReasLib.RingTheory.Unramified.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale Algebras and G-Unramifiedness

This leaf presents Mathlib's canonical `Algebra.Etale` class in terms of the
finite-presentation refinement `Algebra.GUnramified`.
-/

@[expose] public section

universe u v

namespace Algebra.Etale

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- An algebra is etale exactly when it is flat and G-unramified. -/
@[stacks 08WD "etale iff flat and G-unramified"]
theorem iff_flat_and_gUnramified :
    Algebra.Etale R S ↔ Module.Flat R S ∧ Algebra.GUnramified R S := sorry

/-- An algebra is etale exactly when it is flat, unramified, and finitely presented. -/
@[stacks 08WD "etale iff flat, unramified, and finitely presented"]
theorem iff_flat_and_unramified_and_finitePresentation :
    Algebra.Etale R S ↔
      Module.Flat R S ∧ Algebra.Unramified R S ∧ Algebra.FinitePresentation R S := sorry

/-- The etale, flat G-unramified, and flat unramified finite-presentation conditions are
equivalent. -/
@[stacks 08WD]
theorem tfae_flat_gUnramified :
    List.TFAE
      [ Algebra.Etale R S
      , Module.Flat R S ∧ Algebra.GUnramified R S
      , Module.Flat R S ∧ Algebra.Unramified R S ∧ Algebra.FinitePresentation R S
      ] := sorry

end Algebra.Etale
