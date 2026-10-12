/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude.Shift
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Homology
public import ReasLib.CategoryTheory.DerivedCategory.TruncationSplitting
import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude.Triangulated

/-!
# Tor-amplitude from bounded cohomology

@stack 066I

For a bounded derived module object, a uniform Tor-amplitude bound on the intrinsically shifted
cohomology objects gives the same bound on the original object.  The shifted formulation records
the source intervals `[a - i, b - i]` without exposing a choice of bounded complex.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [CommRing R]

/-- Placing a module in degree `i` translates both endpoints of its Tor-amplitude interval. -/
@[stacks 066I "single-object Tor-amplitude interval shift"]
theorem hasTorAmplitudeIn_single_iff
    (M : ModuleCat R) (i a b : ℤ) :
    HasTorAmplitudeIn R ((DerivedCategory.singleFunctor (ModuleCat R) i).obj M) a b ↔
      HasTorAmplitudeIn R ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M)
        (a - i) (b - i) := sorry
/- Proof strategy: identify the degree-`i` single object with the degree-zero single shifted by
`-i`, then apply `DerivedTensor.hasTorAmplitudeIn_shift_iff`. -/

/-- A derived object supported in `[c, c + n]` inherits a common Tor-amplitude interval from
its intrinsically shifted cohomology objects. -/
@[stacks 066I "finite-support shifted-cohomology criterion"]
theorem HasTorAmplitudeIn.of_isGE_isLE_of_shiftedCohomology
    (a b c : ℤ) (n : ℕ) (K : DerivedCategory (ModuleCat R))
    (hGE : K.IsGE c) (hLE : K.IsLE (c + n))
    (hH : ∀ i : Set.Icc c (c + n),
      HasTorAmplitudeIn R
        (DerivedCategory.ShiftedCohomology.family (ModuleCat R) K i.1) a b) :
    HasTorAmplitudeIn R K a b := sorry
/- Proof strategy: induct on `n` with canonical truncation triangles; at each step use the
shifted cohomology hypothesis and the triangulated two-out-of-three API. -/

/-- Lemma 15.67.9 (066I) (1): a bounded derived object has Tor-amplitude in `[a, b]` when
all its intrinsically shifted cohomology objects do. -/
@[stacks 066I "bounded Tor-amplitude from shifted cohomology"]
theorem HasTorAmplitudeIn.of_bounded_of_shiftedCohomology
    (a b : ℤ) (K : DerivedCategory.Bounded (ModuleCat R))
    (hH : ∀ i : ℤ,
      HasTorAmplitudeIn R
        (DerivedCategory.ShiftedCohomology.family (ModuleCat R) K.obj i) a b) :
    HasTorAmplitudeIn R K.obj a b := sorry
/- Proof strategy: obtain finite lower and upper bounds from `K.property`, then invoke
`of_isGE_isLE_of_shiftedCohomology`. -/

/-- Lemma 15.67.9 (Stacks `066I`) (1), source-interval form: if every cohomology module
`Hⁱ(K)`, placed in degree zero, has Tor-amplitude in `[a - i, b - i]`, then the bounded derived
object `K` has Tor-amplitude in `[a, b]`. -/
@[stacks 066I "bounded Tor-amplitude from source-indexed cohomology intervals"]
theorem HasTorAmplitudeIn.of_bounded_of_homology
    (a b : ℤ) (K : DerivedCategory.Bounded (ModuleCat R))
    (hH : ∀ i : ℤ,
      HasTorAmplitudeIn R
        ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
          ((DerivedCategory.Bounded.homologyFunctor (ModuleCat R) i).obj K))
        (a - i) (b - i)) :
    HasTorAmplitudeIn R K.obj a b := sorry
/- Proof strategy: convert each hypothesis with `hasTorAmplitudeIn_single_iff`, identify the
resulting degree-`i` single object with `ShiftedCohomology.family`, and apply
`of_bounded_of_shiftedCohomology`. -/

/-- Lemma 15.67.9 (066I) (2): a bounded derived object whose cohomology modules all have
finite Tor dimension has finite Tor dimension. -/
@[stacks 066I "finite Tor dimension from bounded cohomology"]
theorem HasFiniteTorDimension.of_bounded_of_homology
    (K : DerivedCategory.Bounded (ModuleCat R))
    (hH : ∀ i : ℤ,
      ModuleCat.HasFiniteTorDimension R
        ((DerivedCategory.Bounded.homologyFunctor (ModuleCat R) i).obj K)) :
    HasFiniteTorDimension R K.obj := sorry
/- Proof strategy: only finitely many cohomology objects are nonzero; choose a common interval
from their finite Tor dimensions, translate it with `hasTorAmplitudeIn_single_iff`, and apply
`of_bounded_of_shiftedCohomology`. -/

end CategoryTheory.DerivedCategory
