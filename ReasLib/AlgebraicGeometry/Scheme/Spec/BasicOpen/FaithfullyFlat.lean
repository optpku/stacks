/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.AlgebraicGeometry.Scheme.Spec.BasicOpen.Closure

@[expose] public section

universe u

namespace AlgebraicGeometry.Spec.BasicOpenUnion

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The product of the principal localizations associated to a finite family generating the
unit ideal is faithfully flat over the original ring. -/
theorem localizationProductMap_faithfullyFlat (f : Fin r → R)
    (hf : Ideal.span (Set.range f) = ⊤) :
    (localizationProductMap f).FaithfullyFlat := sorry

end AlgebraicGeometry.Spec.BasicOpenUnion
