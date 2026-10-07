module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude.Triangulated

/-!
# Tor-amplitude from bounded termwise data

For a bounded complex, degreewise Tor-amplitude bounds with the source-prescribed index
translation give a Tor-amplitude bound on the represented derived object.  This file records the
current commutative-ring specialization supplied by the derived tensor facade.

@stack 066H
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [CommRing R]

/-- A zero derived object has Tor-amplitude in every interval. -/
@[stacks 066H "zero-object Tor-amplitude companion"]
theorem HasTorAmplitudeIn.of_isZero
    {K : DerivedCategory (ModuleCat R)} (hK : IsZero K) (a b : ℤ) :
    HasTorAmplitudeIn R K a b := sorry
/- Proof strategy: every tested derived tensor of a zero object is zero, hence lies in every
cohomological interval. -/

/-- Lemma 15.67.8 (066H): a bounded complex whose degree-`i` term has Tor-amplitude in
`[a - i, b - i]` represents an object with Tor-amplitude in `[a, b]`. -/
@[stacks 066H "bounded termwise Tor amplitude"]
theorem HasTorAmplitudeIn.of_bounded_of_termwise
    (a b : ℤ) (K : CochainComplex.Bounded (ModuleCat R))
    (hterm : ∀ i : ℤ,
      HasTorAmplitudeIn R
        ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (K.obj.X i))
        (a - i) (b - i)) :
    HasTorAmplitudeIn R (DerivedCategory.Q.obj K.obj) a b := sorry
/- Proof strategy: induct over the finite support of `K` using stupid truncation triangles and
the three two-out-of-three Tor-amplitude theorems from Stacks `0655`. -/

end CategoryTheory.DerivedCategory
