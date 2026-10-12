/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.PowerImage
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Integrality from power-image generation

This leaf separates the elementary integrality consequence from the definition
of power-image generation.  It remains useful without spectral or tensor-product
infrastructure.
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace PowerImage

/-- Power-image generation is integral when the chosen exponent set contains a positive
exponent. -/
theorem isIntegral
    {f : R →+* S} {E : Set ℕ} (hgen : PowerImage.IsGenerated f E)
    (hpositive : ∃ n ∈ E, 0 < n) :
    f.IsIntegral := sorry

end PowerImage

namespace PowerImage.Pair

/-- A two-power image generation hypothesis is integral as soon as one selected exponent is
positive. -/
theorem isIntegral
    {f : R →+* S} {m n : ℕ} (hgen : Pair.IsGenerated f m n)
    (hpositive : 0 < m ∨ 0 < n) :
    f.IsIntegral := sorry

end PowerImage.Pair

namespace PowerImage.SquareCube

/-- Square/cube image generation is integral. -/
@[stacks 0EUH]
theorem isIntegral
    {f : R →+* S} (hgen : SquareCube.IsGenerated f) :
    f.IsIntegral := sorry

end PowerImage.SquareCube

end RingHom
