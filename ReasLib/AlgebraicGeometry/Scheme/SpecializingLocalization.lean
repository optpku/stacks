/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.RingTheory.Localization.Specializing

@[expose] public section

open AlgebraicGeometry Localization

universe u

namespace Localization.Specializing

variable {A : Type u} [CommRing A]

/-- The morphism from the specializing affine scheme to the basic locally
closed subscheme is a closed immersion. -/
noncomputable instance specMap_toAwayQuotient (f : A) (I : Ideal A) :
    IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (toAwayQuotient f I))) :=
  sorry

end Localization.Specializing
