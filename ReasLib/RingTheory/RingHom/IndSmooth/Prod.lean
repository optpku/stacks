/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.Prod
public import ReasLib.RingTheory.RingHom.IndSmooth.Basic

/-!
# Products of ind-smooth ring maps

The ind-smooth property is stable under binary products of ring maps, without
Noetherian or regularity assumptions on the factors.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace RingHom.IndSmooth

/-- The product of two ind-smooth ring homomorphisms is ind-smooth. -/
@[stacks 07F3]
theorem prodMap
    {R₁ : Type u₁} {A₁ : Type v₁} {R₂ : Type u₂} {A₂ : Type v₂}
    [CommRing R₁] [CommRing A₁] [CommRing R₂] [CommRing A₂]
    {f₁ : R₁ →+* A₁} {f₂ : R₂ →+* A₂}
    (hf₁ : f₁.IndSmooth) (hf₂ : f₂.IndSmooth) :
    (f₁.prodMap f₂).IndSmooth := sorry

end RingHom.IndSmooth
