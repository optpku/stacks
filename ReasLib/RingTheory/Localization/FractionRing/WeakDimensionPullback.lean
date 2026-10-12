/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import ReasLib.RingTheory.Algebra.IsEpi.TensorSquare
public import ReasLib.RingTheory.WeakDimension.Pi
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# A weak-dimension-one pullback over a fraction field

A normal domain inside its fraction field admits a cartesian presentation whose
lower horizontal map is flat, injective, and epic, and whose source has weak
dimension at most one.

@stack 092U
-/

open CategoryTheory Limits CommRingCat

universe u

namespace FractionRing

variable {A K : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
variable [IsFractionRing A K] [IsIntegrallyClosed A]

/-- Lemma 15.105.20: a normal domain and its fraction field fit into a cartesian square whose
lower-left ring has weak dimension at most one and whose lower map is flat, injective, and epic. -/
@[stacks 092U "Lemma 15.105.20"]
theorem exists_pullback_with_weakDimensionLE_one :
    ∃ (V L : CommRingCat.{u}) (i : of A ⟶ V) (k : V ⟶ L) (j : of K ⟶ L),
      IsPullback i (ofHom (algebraMap A K)) k j ∧
        HasWeakDimensionLE V 1 ∧ k.hom.Flat ∧ Function.Injective k.hom ∧ Epi k := sorry

end FractionRing
