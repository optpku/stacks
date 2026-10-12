/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.41.6

@stack 00HZ
-/

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

open AlgebraicGeometry
open PrimeSpectrum

/- Lemma 10.41.6: for the canonical map `Spec(S) → Spec(R)`, the source-facing equivalence is the
affine-spectrum bridge to the canonical owner theorem
`AlgebraicGeometry.isClosedMap_iff_specializingMap`. -/
@[stacks 00HZ]
#check
  (show SpecializingMap (comap (algebraMap R S)) ↔ IsClosedMap (comap (algebraMap R S)) from
    (isClosedMap_iff_specializingMap (Spec.map (CommRingCat.ofHom (algebraMap R S)))).symm)

end
