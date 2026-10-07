module

public import ReasLib.RingTheory.RingHom.BaseChange
public import ReasLib.RingTheory.RingHom.PowerGeneration
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of prime-power generation

The primary API accepts the two ring maps defining a tensor-product base
change.  The ambient-algebra specialization is provided separately for code
already expressed with an `Algebra R R'` instance.
-/

@[expose] public section

universe u v w

namespace RingHom

namespace PowerGeneration

namespace BaseChange

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Prime-power/scalar-image generation is preserved by tensor-product base change along an
arbitrary ring homomorphism. -/
theorem isGenerated
    {p : ℕ} {R' : Type w} [CommRing R']
    (f : R →+* S) (g : R →+* R') (hgen : IsGenerated f p) :
    IsGenerated (f.baseChange g) p := sorry

/-- Ambient-algebra specialization of `BaseChange.isGenerated`. -/
theorem isGenerated_algebraMap
    {p : ℕ} {R' : Type w} [CommRing R'] [Algebra R R']
    (f : R →+* S) (hgen : IsGenerated f p) :
    IsGenerated (f.baseChangeAlgebraMap (R' := R')) p := sorry

end BaseChange

end PowerGeneration

end RingHom
