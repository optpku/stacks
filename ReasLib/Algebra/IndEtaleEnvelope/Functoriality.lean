/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.Algebra.IndEtaleEnvelope.Envelope

/-!
# Functoriality of the ind-étale envelope

The coefficient-pushforward maps on finite presentations induce a commuting
square between the base rings and their ind-étale envelopes.
-/

@[expose] public section

universe u

open CategoryTheory Limits CommRingCat

namespace Algebra.IndEtaleEnvelope

/-- The induced map between ind-étale envelopes commutes with the base-ring
structure maps. -/
theorem map_commSq {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A') :
    CommSq (ofHom (algebraMap A (IndEtaleEnvelope A))) (ofHom φ)
      (ofHom (map φ)) (ofHom (algebraMap A' (IndEtaleEnvelope A'))) :=
  sorry

end Algebra.IndEtaleEnvelope
