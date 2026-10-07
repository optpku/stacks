module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import stacks_project.Chap110.Lemma_110_43_1_Cotangent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent complex of a local complete intersection

Proposition 92.14.4 records that if `A → B` is a local complete intersection
ring map, then the André-Quillen object `L_{B/A}` is perfect in `D(B)` with
Tor-amplitude in `[-1, 0]`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.DerivedTensor

universe u

noncomputable section

namespace Algebra.CotangentComplex

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Proposition 92.14.4. Let `A → B` be a local complete intersection ring map.
Then `L_{B/A}` is a perfect object of `D(B)` with Tor-amplitude in `[-1, 0]`. -/
@[stacks 08SL]
theorem isPerfect_and_hasTorAmplitudeIn_of_lci
    (hf : (algebraMap A B).IsLocalCompleteIntersection) :
    DerivedCategory.IsPerfect (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) ∧
      HasTorAmplitudeIn (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) (-1) 0 :=
  sorry

/-- If `A → B` is a local complete intersection, then `L_{B/A}` is perfect in `D(B)`. -/
theorem isPerfect_of_lci (hf : (algebraMap A B).IsLocalCompleteIntersection) :
    DerivedCategory.IsPerfect (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) :=
  sorry

/-- If `A → B` is a local complete intersection, then `L_{B/A}` has Tor-amplitude in
`[-1, 0]`. -/
theorem hasTorAmplitudeIn_of_lci (hf : (algebraMap A B).IsLocalCompleteIntersection) :
    HasTorAmplitudeIn (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) (-1) 0 :=
  sorry

end

/-- If `A → B` is a local complete intersection ring map, then `L_{B/A}` is perfect in
`D(B)` with Tor-amplitude in `[-1, 0]`. -/
theorem ringHom_isPerfect_and_hasTorAmplitudeIn_of_lci {A B : Type u}
    [CommRing A] [CommRing B] {f : A →+* B} (hf : f.IsLocalCompleteIntersection) :
    DerivedCategory.IsPerfect (DerivedCategory.Q.obj (RingHom.cotangentComplex f)) ∧
      HasTorAmplitudeIn (DerivedCategory.Q.obj (RingHom.cotangentComplex f)) (-1) 0 :=
  sorry

end Algebra.CotangentComplex
