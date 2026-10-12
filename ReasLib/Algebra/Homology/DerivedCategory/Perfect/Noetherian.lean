/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Characterization
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Noetherian
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Over a commutative Noetherian ring, a derived module object is perfect if and only if
it has finite Tor dimension and finite homology in every degree. -/
@[stacks 03TO]
theorem isPerfect_iff_hasFiniteTorDimension_and_finite_homology
    (K : DerivedCategory (ModuleCat R)) :
    K.IsPerfect ↔
      HasFiniteTorDimension R K ∧
        ∀ i : ℤ, Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K) := sorry

/-- Over a commutative Noetherian ring, every homology module of a perfect derived
module object is finite. -/
theorem IsPerfect.homology_finite {K : DerivedCategory (ModuleCat R)}
    (hK : K.IsPerfect) :
    ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K) := sorry

/-- Over a commutative Noetherian ring, a derived module object of finite Tor dimension
with finite homology in every degree is perfect. -/
theorem isPerfect_of_hasFiniteTorDimension_of_finite_homology
    {K : DerivedCategory (ModuleCat R)} (hTor : HasFiniteTorDimension R K)
    (hH : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K)) :
    K.IsPerfect := sorry

end CategoryTheory.DerivedCategory
