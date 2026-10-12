/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.FiniteTypeLocal
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation

@[expose] public section

universe u v w x

/-- The ring homomorphism from `A_f` to `B_(φ(f) * g)` induced by a ring map
`φ : A →+* B` and the two indicated basic-open elements. -/
noncomputable def Localization.awayMulMap {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) (a : A) (b : B) :
    Localization.Away a →+* Localization.Away (φ a * b) :=
  (IsLocalization.Away.awayToAwayRight (φ a) b :
      Localization.Away (φ a) →+* Localization.Away (φ a * b)).comp
    (Localization.awayMap φ a)

/-- The mixed localization map is compatible with the algebra maps from the source and target
rings. -/
theorem Localization.awayMulMap_comp_algebraMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (φ : A →+* B) (a : A) (b : B) :
    (Localization.awayMulMap φ a b).comp (algebraMap A (Localization.Away a)) =
      (algebraMap B (Localization.Away (φ a * b))).comp φ := sorry

/-- Finite type of an algebra map can be checked on simultaneous basic-open covers of its source
and target. -/
theorem Algebra.FiniteType.of_basicOpen_cover
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type w} {κ : Type x} (f : ι → A) (g : κ → B)
    (hf : (⨆ i, PrimeSpectrum.basicOpen (f i)) = ⊤)
    (hg : (⨆ j, PrimeSpectrum.basicOpen (g j)) = ⊤)
    (h : ∀ i j, (Localization.awayMulMap (algebraMap A B) (f i) (g j)).FiniteType) :
    Algebra.FiniteType A B := sorry
