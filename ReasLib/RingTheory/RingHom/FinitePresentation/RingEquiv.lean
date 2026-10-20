/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely presented ring maps under ring equivalences

This leaf records transport of finite presentation along an isomorphism square
in the category of commutative rings.  Algebra presentations are recovered
through `RingHom.finitePresentation_algebraMap` at a consumer that genuinely
uses an algebra map.
-/

@[expose] public section

universe u v w x

namespace RingHom.FinitePresentation

variable {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']

/-- Finite presentation is preserved by a commuting square of ring equivalences. -/
@[stacks 051X "finite-presentation transport under compatible ring equivalences"]
theorem of_ringEquiv
    {f : R →+* S} {f' : R' →+* S'}
    (eR : R ≃+* R') (eS : S ≃+* S')
    (hcomm : ∀ r : R, eS (f r) = f' (eR r))
    (hf : f.FinitePresentation) :
    f'.FinitePresentation := sorry

end RingHom.FinitePresentation
