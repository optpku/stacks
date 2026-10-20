module

public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.IndEtale.Basic

@[expose] public section

/-!
# Base change for ind-etale ring maps

The owner-level predicate is stable under arbitrary tensor-product base change.
The concrete tensor-product corollary is retained because it is the normal
consumer interface for commutative algebras.
-/

open scoped TensorProduct

universe u v

namespace RingHom

namespace IndEtale

/-- Ind-etale ring maps are stable under base change. -/
@[stacks 0BSH "ind-etale base change"]
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) =>
        f.IndEtale) := sorry

end IndEtale

namespace IndEtale.Raw

/-- Arbitrary-size ind-etale presentations are stable under base change. -/
@[stacks 0BSH "ind-etale base change"]
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) =>
        RingHom.IndEtale.Raw.{u, u, v} f) := sorry

end IndEtale.Raw

namespace IndEtale.Raw

section

variable {R A R' : Type u}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/-- Tensor-product base change preserves ind-etale presentations at an arbitrary
presentation universe. -/
@[stacks 0BSH "ind-etale base change"]
theorem baseChange
    (hA : RingHom.IndEtale.Raw.{u, u, v} (algebraMap R A)) :
    RingHom.IndEtale.Raw.{u, u, v} (algebraMap R' (R' ⊗[R] A)) := sorry

end

end IndEtale.Raw

namespace IndEtale

/-- Tensor-product base change of an ind-etale algebra map is ind-etale. -/
@[stacks 0BSH "ind-etale base change"]
theorem baseChange
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (hA : (algebraMap R A).IndEtale) :
    (algebraMap R' (R' ⊗[R] A)).IndEtale := sorry

end IndEtale

end RingHom
