module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute

/-!
# Characterizing Perfect Derived Objects

@stack 0658

Perfectness is equivalent to pseudo-coherence together with finite Tor dimension.  The
projection lemmas below are the small API most downstream arguments need.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [CommRing R]

/-- A derived module object is perfect exactly when it is pseudo-coherent and has finite
Tor dimension. -/
@[stacks 0658 "perfect iff pseudo-coherent of finite Tor dimension"]
theorem isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
    (K : DerivedCategory (ModuleCat R)) :
    K.IsPerfect ↔ K.IsPseudoCoherent ∧ HasFiniteTorDimension R K := sorry

/-- Every perfect derived module object is pseudo-coherent. -/
theorem IsPerfect.isPseudoCoherent {K : DerivedCategory (ModuleCat R)}
    (hK : K.IsPerfect) :
    K.IsPseudoCoherent := sorry

/-- Every perfect derived module object has finite Tor dimension. -/
theorem IsPerfect.hasFiniteTorDimension {K : DerivedCategory (ModuleCat R)}
    (hK : K.IsPerfect) :
    HasFiniteTorDimension R K := sorry

/-- A pseudo-coherent object with Tor-amplitude in `[a, b]` has a finite-projective model
supported in the same interval. -/
@[stacks 0658 "finite-projective model in a Tor-amplitude interval"]
theorem IsPseudoCoherent.exists_finiteProjective_model
    {K : DerivedCategory (ModuleCat R)} {a b : ℤ}
    (hK : K.IsPseudoCoherent) (hamp : HasTorAmplitudeIn R K a b) :
    ∃ E : CochainComplex (ModuleCat R) ℤ,
      ∃ (_ : K ≅ DerivedCategory.Q.obj E), E.IsFiniteProjectiveIn a b := sorry

end CategoryTheory.DerivedCategory
