/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.RingHom.Perfect.Basic
public import ReasLib.RingTheory.RingHom.Syntomic.LocalCompleteIntersection

/-!
# Tor amplitude of naive cotangent objects

This leaf relates the canonical map-first naive cotangent object to perfect,
local-complete-intersection, and syntomic ring homomorphisms. Tor amplitude is expressed through
the generic monoidal derived-category object property, so the statements do not install a local
derived-category instance or depend on an ambient `Algebra` instance.

Mathlib's monoidal structure on `ModuleCat.{w} R` currently requires `R : Type w`.  The canonical
self-presentation of a map `A → B` lives in module universe `max u v`, so the target ring is placed
in `Type (max u v)` below.  This is an actual upstream monoidal-universe boundary, not a local
instance that should be reconstructed in this leaf.

@stack 0FV0
@stack 0FJT
@stack 0FJV
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory.DerivedTensor

universe u v

namespace RingHom.NaiveCotangent

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B]

/-- A local-complete-intersection map has a perfect naive cotangent object. -/
@[stacks 0FV0 "perfectness component"]
theorem isPerfect_of_lci {f : A →+* B} (hf : f.IsLocalCompleteIntersection) :
    DerivedCategory.IsPerfect f.naiveCotangentObject := sorry
/- Proof strategy: choose local complete-intersection polynomial presentations of `f`; their
two-term conormal-to-differentials complexes have finite projective terms, hence give a perfect
model for the canonical naive cotangent object.  Descend the local models through the existing
perfect-object localization criterion. -/

/-- A local-complete-intersection map has naive cotangent Tor amplitude in `[-1, 0]`. -/
@[stacks 0FV0 "Tor-amplitude component"]
theorem hasTorAmplitudeIn_of_lci {f : A →+* B} (hf : f.IsLocalCompleteIntersection) :
    HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 := sorry
/- Proof strategy: use the same local two-term finite-projective models; tensoring such a complex
has homology only in degrees `-1` and `0`, and Tor amplitude is detected after localization. -/

/-- Lemma 15.86.4 (0FV0): a local-complete-intersection map has a perfect naive cotangent
object of Tor amplitude `[-1, 0]`. -/
@[stacks 0FV0 "perfectness and Tor-amplitude of the naive cotangent complex"]
theorem isPerfect_and_hasTorAmplitudeIn_of_lci
    {f : A →+* B} (hf : f.IsLocalCompleteIntersection) :
    DerivedCategory.IsPerfect f.naiveCotangentObject ∧
      HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 := sorry
/- Proof strategy: pair `isPerfect_of_lci hf` with `hasTorAmplitudeIn_of_lci hf`. -/

/-- A syntomic map has a perfect naive cotangent object. -/
@[stacks 0FJV "syntomic perfectness component"]
theorem isPerfect_of_syntomic {f : A →+* B} (hf : f.Syntomic) :
    DerivedCategory.IsPerfect f.naiveCotangentObject := sorry
/- Proof strategy: extract the local-complete-intersection component of `hf` and apply
`isPerfect_of_lci`. -/

/-- A syntomic map has naive cotangent Tor amplitude in `[-1, 0]`. -/
@[stacks 0FJV "syntomic Tor-amplitude component"]
theorem hasTorAmplitudeIn_of_syntomic {f : A →+* B} (hf : f.Syntomic) :
    HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 := sorry
/- Proof strategy: extract the local-complete-intersection component of `hf` and apply
`hasTorAmplitudeIn_of_lci`. -/

/-- A syntomic map has a perfect naive cotangent object of Tor amplitude in `[-1, 0]`. -/
@[stacks 0FJV "syntomic perfectness and Tor-amplitude"]
theorem isPerfect_and_hasTorAmplitudeIn_of_syntomic
    {f : A →+* B} (hf : f.Syntomic) :
    DerivedCategory.IsPerfect f.naiveCotangentObject ∧
      HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 := sorry
/- Proof strategy: pair `isPerfect_of_syntomic hf` with `hasTorAmplitudeIn_of_syntomic hf`. -/

end RingHom.NaiveCotangent

namespace RingHom.IsPerfectRingMap.NaiveCotangent

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- For a perfect map of Noetherian rings, Tor amplitude `[-1, 0]` of the naive cotangent object
implies that the map is a local complete intersection. -/
@[stacks 0FJT "Tor-amplitude implies local complete intersection"]
theorem lci_of_hasTorAmplitudeIn
    {f : A →+* B} (hperfect : f.IsPerfectRingMap)
    (hTor : HasTorAmplitudeIn f.naiveCotangentObject (-1) 0) :
    f.IsLocalCompleteIntersection := sorry
/- Proof strategy: use perfectness to obtain a pseudo-coherent finite presentation of the map.
The Tor-amplitude bound makes the conormal module projective after localization; apply the
Noetherian cotangent criterion for local complete intersections and descend from the local
presentations. -/

/-- For a perfect map of Noetherian rings, Tor amplitude `[-1, 0]` makes the naive cotangent
object perfect. -/
@[stacks 0FJT "Tor-amplitude implies perfect naive cotangent"]
theorem isPerfect_of_hasTorAmplitudeIn
    {f : A →+* B} (hperfect : f.IsPerfectRingMap)
    (hTor : HasTorAmplitudeIn f.naiveCotangentObject (-1) 0) :
    DerivedCategory.IsPerfect f.naiveCotangentObject := sorry
/- Proof strategy: obtain `f.IsLocalCompleteIntersection` from
`lci_of_hasTorAmplitudeIn hperfect hTor`, then apply `RingHom.NaiveCotangent.isPerfect_of_lci`. -/

/-- Lemma 23.11.4 (0FJT), clauses (1) and (2): for a perfect map of Noetherian rings, Tor
amplitude `[-1, 0]` of the naive cotangent object already implies its perfectness. -/
@[stacks 0FJT "(1) iff (2)"]
theorem hasTorAmplitudeIn_iff_isPerfect_and
    {f : A →+* B} (hperfect : f.IsPerfectRingMap) :
    HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 ↔
      DerivedCategory.IsPerfect f.naiveCotangentObject ∧
        HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 := sorry
/- Proof strategy: the reverse implication is projection to the Tor-amplitude conjunct; the
forward implication pairs `isPerfect_of_hasTorAmplitudeIn hperfect` with the original bound. -/

/-- Lemma 23.11.4 (0FJT), clauses (1) and (3): for a perfect map of Noetherian rings, the naive
cotangent object has Tor amplitude `[-1, 0]` exactly when the map is a local complete
intersection. -/
@[stacks 0FJT "(1) iff (3)"]
theorem hasTorAmplitudeIn_iff_lci
    {f : A →+* B} (hperfect : f.IsPerfectRingMap) :
    HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 ↔
      f.IsLocalCompleteIntersection := sorry
/- Proof strategy: use `lci_of_hasTorAmplitudeIn hperfect` in the forward direction and
`RingHom.NaiveCotangent.hasTorAmplitudeIn_of_lci` in the reverse direction. -/

/-- Lemma 23.11.4 (0FJT), clauses (2) and (3): for a perfect map of Noetherian rings, a perfect
naive cotangent object of Tor amplitude `[-1, 0]` is equivalent to the map being a local complete
intersection. -/
@[stacks 0FJT "(2) iff (3)"]
theorem isPerfect_and_hasTorAmplitudeIn_iff_lci
    {f : A →+* B} (hperfect : f.IsPerfectRingMap) :
    (DerivedCategory.IsPerfect f.naiveCotangentObject ∧
      HasTorAmplitudeIn f.naiveCotangentObject (-1) 0) ↔
        f.IsLocalCompleteIntersection := sorry
/- Proof strategy: compose `hasTorAmplitudeIn_iff_isPerfect_and hperfect` symmetrically with
`hasTorAmplitudeIn_iff_lci hperfect`. -/

end RingHom.IsPerfectRingMap.NaiveCotangent

namespace RingHom.Flat.NaiveCotangent

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B]

/-- For a flat finitely presented map, Tor amplitude `[-1, 0]` makes the naive cotangent object
perfect. -/
@[stacks 0FJV "flat finite-presentation perfectness component"]
theorem isPerfect_of_hasTorAmplitudeIn
    {f : A →+* B} (hflat : f.Flat) (hfp : f.FinitePresentation)
    (hTor : HasTorAmplitudeIn f.naiveCotangentObject (-1) 0) :
    DerivedCategory.IsPerfect f.naiveCotangentObject := sorry
/- Proof strategy: finite presentation gives pseudo-coherence of the naive cotangent object;
combine it with the finite Tor-amplitude interval and the pseudo-coherent-plus-finite-Tor
criterion for perfect derived objects. -/

/-- For a flat finitely presented map, naive cotangent Tor amplitude `[-1, 0]` implies
syntomicity. -/
@[stacks 0FJV "Tor-amplitude implies syntomic"]
theorem syntomic_of_hasTorAmplitudeIn
    {f : A →+* B} (hflat : f.Flat) (hfp : f.FinitePresentation)
    (hTor : HasTorAmplitudeIn f.naiveCotangentObject (-1) 0) :
    f.Syntomic := sorry
/- Proof strategy: prove the LCI condition with `lci_of_hasTorAmplitudeIn hflat hfp hTor`, then
combine it with the supplied flatness and finite-presentation hypotheses using the canonical
characterization of syntomic maps. -/

/-- For a flat finitely presented map, naive cotangent Tor amplitude `[-1, 0]` implies the local
complete-intersection condition. -/
@[stacks 0FJV "Tor-amplitude implies local complete intersection"]
theorem lci_of_hasTorAmplitudeIn
    {f : A →+* B} (hflat : f.Flat) (hfp : f.FinitePresentation)
    (hTor : HasTorAmplitudeIn f.naiveCotangentObject (-1) 0) :
    f.IsLocalCompleteIntersection := sorry
/- Proof strategy: use a finite presentation of `f`.  Flatness identifies the derived and
underived cotangent base-change models, while the Tor-amplitude bound makes the conormal module
projective; apply the presentation criterion for local complete intersections. -/

/-- Lemma 23.11.5 (0FJV), clauses (1) and (2): for a flat finitely presented map, Tor amplitude
`[-1, 0]` of the naive cotangent object already implies its perfectness. -/
@[stacks 0FJV "(1) iff (2)"]
theorem hasTorAmplitudeIn_iff_isPerfect_and
    {f : A →+* B} (hflat : f.Flat) (hfp : f.FinitePresentation) :
    HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 ↔
      DerivedCategory.IsPerfect f.naiveCotangentObject ∧
        HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 := sorry
/- Proof strategy: the reverse implication is projection; the forward implication pairs
`isPerfect_of_hasTorAmplitudeIn hflat hfp` with the assumed Tor-amplitude bound. -/

/-- Lemma 23.11.5 (0FJV), clauses (1) and (3): for a flat finitely presented map, the naive
cotangent object has Tor amplitude `[-1, 0]` exactly when the map is syntomic. -/
@[stacks 0FJV "(1) iff (3)"]
theorem hasTorAmplitudeIn_iff_syntomic
    {f : A →+* B} (hflat : f.Flat) (hfp : f.FinitePresentation) :
    HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 ↔ f.Syntomic := sorry
/- Proof strategy: use `syntomic_of_hasTorAmplitudeIn hflat hfp` forward and
`RingHom.NaiveCotangent.hasTorAmplitudeIn_of_syntomic` backward. -/

/-- Lemma 23.11.5 (0FJV), clauses (1) and (4): for a flat finitely presented map, the naive
cotangent object has Tor amplitude `[-1, 0]` exactly when the map is a local complete
intersection. -/
@[stacks 0FJV "(1) iff (4)"]
theorem hasTorAmplitudeIn_iff_lci
    {f : A →+* B} (hflat : f.Flat) (hfp : f.FinitePresentation) :
    HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 ↔
      f.IsLocalCompleteIntersection := sorry
/- Proof strategy: use `lci_of_hasTorAmplitudeIn hflat hfp` forward and
`RingHom.NaiveCotangent.hasTorAmplitudeIn_of_lci` backward. -/

/-- Lemma 23.11.5 (0FJV), clauses (2) and (3): for a flat finitely presented map, perfectness
and Tor amplitude `[-1, 0]` of the naive cotangent object are equivalent to syntomicity. -/
@[stacks 0FJV "(2) iff (3)"]
theorem isPerfect_and_hasTorAmplitudeIn_iff_syntomic
    {f : A →+* B} (hflat : f.Flat) (hfp : f.FinitePresentation) :
    (DerivedCategory.IsPerfect f.naiveCotangentObject ∧
      HasTorAmplitudeIn f.naiveCotangentObject (-1) 0) ↔ f.Syntomic := sorry
/- Proof strategy: compose `hasTorAmplitudeIn_iff_isPerfect_and hflat hfp` symmetrically with
`hasTorAmplitudeIn_iff_syntomic hflat hfp`. -/

/-- Lemma 23.11.5 (0FJV), clauses (2) and (4): for a flat finitely presented map, perfectness
and Tor amplitude `[-1, 0]` of the naive cotangent object are equivalent to the local
complete-intersection condition. -/
@[stacks 0FJV "(2) iff (4)"]
theorem isPerfect_and_hasTorAmplitudeIn_iff_lci
    {f : A →+* B} (hflat : f.Flat) (hfp : f.FinitePresentation) :
    (DerivedCategory.IsPerfect f.naiveCotangentObject ∧
      HasTorAmplitudeIn f.naiveCotangentObject (-1) 0) ↔
        f.IsLocalCompleteIntersection := sorry
/- Proof strategy: compose `hasTorAmplitudeIn_iff_isPerfect_and hflat hfp` symmetrically with
`hasTorAmplitudeIn_iff_lci hflat hfp`. -/

end RingHom.Flat.NaiveCotangent
