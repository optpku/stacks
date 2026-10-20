/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHomProperties
public import ReasLib.RingTheory.RingHom.IndZariski

@[expose] public section

open scoped TensorProduct

universe u v

namespace RingHom

namespace IndZariski

/-- Ind-Zariski ring maps are stable under arbitrary tensor-product base change. -/
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        f.IndZariski) := sorry

/-- The tensor-product base change of an ind-Zariski algebra map is ind-Zariski. -/
theorem baseChange
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (hA : (algebraMap R A).IndZariski) :
    (algebraMap R' (R' ⊗[R] A)).IndZariski := sorry

end IndZariski

namespace IndZariski.Raw

/-- Arbitrary-size ind-Zariski presentations are stable under tensor-product base change. -/
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        RingHom.IndZariski.Raw.{u, u, v} f) := sorry

section

variable {R A R' : Type u}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/-- Tensor-product base change preserves ind-Zariski presentations at an arbitrary presentation universe. -/
theorem baseChange
    (hA : RingHom.IndZariski.Raw.{u, u, v} (algebraMap R A)) :
    RingHom.IndZariski.Raw.{u, u, v} (algebraMap R' (R' ⊗[R] A)) := sorry

end

end IndZariski.Raw

end RingHom
