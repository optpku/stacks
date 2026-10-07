module

public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.RingTheory.WeakDimension
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor-amplitude and dimension bounds

@stack 066P

A uniform weak-dimension bound controls the Tor-amplitude of every cohomologically bounded
derived module.  A global-dimension bound supplies the required weak-dimension instance, giving
the source-facing specialization without baking projective resolutions into the derived API.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace HasWeakDimensionLE

variable {R : Type u} [CommRing R]

/-- A weak-dimension bound enlarges a cohomological interval by at most `d` on the left when
viewed as a Tor-amplitude interval. -/
@[stacks 066P "weak dimension controls Tor amplitude"]
theorem hasTorAmplitudeIn (d : ℕ) [HasWeakDimensionLE R d]
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ)
    (hGE : K.IsGE a) (hLE : K.IsLE b) :
    DerivedCategory.HasTorAmplitudeIn (R := R) K (a - (d : ℤ)) b := sorry
/- Proof strategy: tensor `K` with an arbitrary degree-zero module, use the weak-dimension bound
to control the leftward homological spread by `d`, and retain the upper bound from `hLE`. -/

/-- Over a ring of weak dimension at most `d`, finite Tor dimension is equivalent to bounded
cohomology. -/
@[stacks 066P "weak dimension and finite Tor dimension"]
theorem hasFiniteTorDimension_iff_bounded (d : ℕ) [HasWeakDimensionLE R d]
    (K : DerivedCategory (ModuleCat R)) :
    DerivedCategory.HasFiniteTorDimension (R := R) K ↔
      DerivedCategory.TStructure.t.bounded K := sorry
/- Proof strategy: a finite Tor-amplitude interval forces bounded cohomology by testing against
the unit module; conversely, choose cohomological bounds and apply
`HasWeakDimensionLE.hasTorAmplitudeIn`. -/

end HasWeakDimensionLE

namespace HasGlobalDimensionLE

variable {R : Type u} [CommRing R]

/-- Lemma 15.67.19 (1): a global-dimension bound supplies the same Tor-dimension bound for every
module. -/
@[stacks 066P "Lemma 15.67.19 (1)"]
theorem hasTorDimensionLE (d : ℕ) [HasGlobalDimensionLE R d]
    (M : ModuleCat R) :
    ModuleCat.HasTorDimensionLE (R := R) M d := sorry
/- Proof strategy: take a projective resolution of `M` of length at most `d`, regard it as a
finite flat resolution, and apply the finite-flat-resolution characterization of Tor dimension. -/

/-- Lemma 15.67.19 (2): a global-dimension bound controls Tor-amplitude from a cohomological
support interval. -/
@[stacks 066P "Lemma 15.67.19 (2)"]
theorem hasTorAmplitudeIn (d : ℕ) [HasGlobalDimensionLE R d]
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ)
    (hGE : K.IsGE a) (hLE : K.IsLE b) :
    DerivedCategory.HasTorAmplitudeIn (R := R) K (a - (d : ℤ)) b := sorry
/- Proof strategy: obtain the corresponding weak-dimension bound from global dimension and apply
`HasWeakDimensionLE.hasTorAmplitudeIn`. -/

/-- Lemma 15.67.19 (3): over a ring of global dimension at most `d`, finite Tor dimension is
equivalent to bounded cohomology. -/
@[stacks 066P "Lemma 15.67.19 (3)"]
theorem hasFiniteTorDimension_iff_bounded (d : ℕ) [HasGlobalDimensionLE R d]
    (K : DerivedCategory (ModuleCat R)) :
    DerivedCategory.HasFiniteTorDimension (R := R) K ↔
      DerivedCategory.TStructure.t.bounded K := sorry
/- Proof strategy: pass from global dimension to weak dimension and invoke
`HasWeakDimensionLE.hasFiniteTorDimension_iff_bounded`. -/

end HasGlobalDimensionLE

namespace CategoryTheory.DerivedCategory.HasTorAmplitudeIn

variable {R : Type u} [CommRing R]

/-- Tor-amplitude in `[a, b]` forces ordinary cohomology to vanish outside `[a, b]`. -/
@[stacks 066P "Tor amplitude controls ordinary homology support"]
theorem isZero_homology_of_not_mem
    {K : DerivedCategory (ModuleCat R)} {a b i : ℤ}
    (hK : HasTorAmplitudeIn (R := R) K a b) (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K) := sorry
/- Proof strategy: specialize `hK` to the degree-zero unit module, identify derived tensoring
with that unit with `K`, and transport the asserted homology vanishing across the unit
comparison. -/

end CategoryTheory.DerivedCategory.HasTorAmplitudeIn
