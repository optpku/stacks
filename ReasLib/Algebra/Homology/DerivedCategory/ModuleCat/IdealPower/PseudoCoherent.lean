/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Cohomology
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo-coherent ideal-power derived tensor systems

Over a Noetherian ring, pseudo-coherence supplies both Mittag-Leffler cohomology systems and the
comparison between their limits and the corresponding ideal-power quotient limits.
@stack 0EGV
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower.HomologySystem

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The cohomology of the ideal-power derived tensor system of a pseudo-coherent object satisfies
the Mittag-Leffler condition in every degree. -/
@[stacks 0EGV "Mittag-Leffler ideal-power tensor cohomology"]
theorem isMittagLeffler_of_isPseudoCoherent
    (I : Ideal A)
    {K : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u, u} A)}
    (hK : K.IsPseudoCoherent) (i : ℤ) :
    (IdealPower.homologySystem I K i).IsMittagLeffler := sorry

/-- For a pseudo-coherent object, the limit of the cohomology quotient system is isomorphic to
the limit of the cohomology of its ideal-power derived tensor system. -/
@[stacks 0EGV "pseudo-coherent ideal-power quotient limit comparison"]
theorem quotientLimit_of_isPseudoCoherent
    (I : Ideal A)
    {K : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u, u} A)}
    (hK : K.IsPseudoCoherent) (i : ℤ) :
    IsIsomorphic
      (limit (Ideal.PowerQuotient.positiveSystem I
        ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K)))
      (limit (IdealPower.homologySystem I K i)) := sorry

/-- Adic-completion presentation of the pseudo-coherent ideal-power cohomology limit
comparison. -/
@[stacks 0EGV "pseudo-coherent adic cohomology limit comparison"]
theorem adicLimit_of_isPseudoCoherent
    (I : Ideal A)
    {K : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u, u} A)}
    (hK : K.IsPseudoCoherent) (i : ℤ) :
    IsIsomorphic
      (ModuleCat.of A
        (AdicCompletion I
          ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K)))
      (limit (IdealPower.homologySystem I K i)) := sorry

end CategoryTheory.DerivedCategory.IdealPower.HomologySystem
