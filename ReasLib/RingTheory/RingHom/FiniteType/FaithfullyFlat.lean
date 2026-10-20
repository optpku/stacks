/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Descent
import ReasLib.RingTheory.RingHom.FaithfullyFlat.Approximation

@[expose] public section

universe u v w

namespace RingHom.FiniteType

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable {f : R →+* A} {g : A →+* B}

/-- Finite type descends from a composite along a faithfully flat, finitely
presented second map. -/
theorem of_comp_of_faithfullyFlat_of_finitePresentation
    (hcomp : (g.comp f).FiniteType) (hfaithfullyFlat : g.FaithfullyFlat)
    (hfinitePresentation : g.FinitePresentation) :
    f.FiniteType := sorry

end RingHom.FiniteType
