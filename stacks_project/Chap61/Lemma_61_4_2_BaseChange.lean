module

public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap61.Definition_61_4_1_IndZariski

@[expose] public section

/-!
# Base change of ind-Zariski ring maps

The owner-level predicate is stable under arbitrary tensor-product base change.
The concrete tensor-product corollary is the normal consumer interface for
commutative algebras.
-/

open scoped TensorProduct

universe u v

namespace RingHom

namespace IndZariski

/-- Ind-Zariski ring maps are stable under base change. -/
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        f.IndZariski) := sorry

/-- The tensor-product base change of an ind-Zariski algebra map is
ind-Zariski. -/
@[stacks 096P "ind-Zariski base change"]
theorem baseChange
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (hA : (algebraMap R A).IndZariski) :
    (algebraMap R' (R' ⊗[R] A)).IndZariski := sorry

end IndZariski

namespace IndZariski.Raw

/-- Arbitrary-size ind-Zariski presentations are stable under base change. -/
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        RingHom.IndZariski.Raw.{u, u, v} f) := sorry

section

variable {R A R' : Type u}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/-- Tensor-product base change preserves ind-Zariski presentations at an
arbitrary presentation universe. -/
theorem baseChange
    (hA : RingHom.IndZariski.Raw.{u, u, v} (algebraMap R A)) :
    RingHom.IndZariski.Raw.{u, u, v} (algebraMap R' (R' ⊗[R] A)) := sorry

end

end IndZariski.Raw

end RingHom
