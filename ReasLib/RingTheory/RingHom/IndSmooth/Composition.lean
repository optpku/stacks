/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndSmooth.Basic

@[expose] public section

/-!
# Composition of ind-smooth ring maps

This leaf owns the map-first composition API for the canonical ind-smooth
predicate. The categorical presentation universe remains hidden in
`RingHom.IndSmooth.Raw`.
-/

universe u v w

namespace RingHom.IndSmooth

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]

/-- A composite of ind-smooth ring maps is ind-smooth. -/
theorem comp (f : A →+* B) (g : B →+* C)
    (hf : f.IndSmooth) (hg : g.IndSmooth) :
    (g.comp f).IndSmooth := sorry

end RingHom.IndSmooth
