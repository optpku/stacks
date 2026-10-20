module

public import Mathlib.RingTheory.Smooth.Local
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Local
public import ReasLib.RingTheory.Extension.Presentation.Jacobian.Fin
public import ReasLib.RingTheory.Smooth.AtPrime

@[expose] public section

/-!
# Jacobian Criteria at a Prime

This leaf gives the primewise and global Jacobian criteria for a fixed
relative-global-complete-intersection presentation. The embedding-indexed
Jacobian ideal itself belongs to `Extension.Presentation.Jacobian`.
@stack 00TE
-/

universe u v

namespace Algebra.Presentation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {n c : ℕ}

namespace Jacobian

/-- A Jacobian column minor of a finite presentation that avoids a target
prime implies smoothness at that prime. -/
theorem isSmoothAt_of_columnMinor_not_mem
    {P : Presentation R S (Fin n) (Fin c)} (q : PrimeSpectrum S)
    (I : Set.powersetCard (Fin n) c)
    (hI : algebraMap P.Ring S
      (P.jacobianColumnMinor (Fin.castLEEmb le_rfl) I) ∉ q.asIdeal) :
    IsSmoothAt R q.asIdeal := sorry

end Jacobian

namespace IsRelativeGlobalCompleteIntersection.Jacobian

/-- For a relative global complete-intersection presentation, smoothness at a
prime is equivalent to the Jacobian minor ideal not being contained in that
prime. -/
theorem isSmoothAt_iff_not_le
    {P : Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) (q : PrimeSpectrum S) :
    IsSmoothAt R q.asIdeal ↔
      ¬ (P.jacobianIdeal (Fin.castLEEmb le_rfl) ≤ q.asIdeal) := sorry

/-- For a relative global complete-intersection presentation, smoothness at a
prime is equivalent to a Jacobian column minor avoiding that prime. -/
@[stacks 00TE "Jacobian criterion at a prime"]
theorem isSmoothAt_iff_exists_minor_not_mem
    {P : Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) (q : PrimeSpectrum S) :
    IsSmoothAt R q.asIdeal ↔
      ∃ I : Set.powersetCard (Fin n) c,
        algebraMap P.Ring S
          (P.jacobianColumnMinor (Fin.castLEEmb le_rfl) I) ∉ q.asIdeal := sorry

/-- The Stacks-style primewise smoothness predicate has the same Jacobian
minor criterion for a relative global complete-intersection presentation. -/
theorem smoothAtPrime_iff_exists_minor_not_mem
    {P : Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) (q : PrimeSpectrum S) :
    SmoothAtPrime R S q ↔
      ∃ I : Set.powersetCard (Fin n) c,
        algebraMap P.Ring S
          (P.jacobianColumnMinor (Fin.castLEEmb le_rfl) I) ∉ q.asIdeal := sorry

/-- A relative global complete-intersection presentation is smooth precisely
when its Jacobian minor ideal is the unit ideal. -/
theorem smooth_iff_ideal_eq_top
    {P : Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    Smooth R S ↔ P.jacobianIdeal (Fin.castLEEmb le_rfl) = ⊤ := sorry

end IsRelativeGlobalCompleteIntersection.Jacobian

end Algebra.Presentation
