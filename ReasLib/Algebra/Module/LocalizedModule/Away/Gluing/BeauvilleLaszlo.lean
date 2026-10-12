/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.RingTheory.Ideal.Principal

import Mathlib.Tactic.CrossRefAttribute

/-!
# Beauville-Laszlo glueing pairs

This file owns the two maps in the Beauville-Laszlo Cech sequence, the comparison on power
torsion, and the glueing-pair predicate.  The exactness criteria identify the three terms of the
Cech sequence with the injective and surjective parts of the torsion comparison.

@stack 0BNR
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

variable {R R' : Type u} [CommRing R] [CommRing R']

/-- The image of an `f`-power-torsion element under a ring homomorphism is again
`f`-power torsion. -/
@[stacks 0BNR "power torsion is preserved by scalar extension"]
theorem algebraMap_mem_fPowerTorsion
    (φ : R →+* R') (f : R)
    (x : Submodule.torsion' R R (Submonoid.powers f)) :
    let _ : Algebra R R' := φ.toAlgebra
    (Algebra.linearMap R R') (x : R) ∈
      Submodule.torsion' R R' (Submonoid.powers f) := sorry

/-- The canonical map on `f`-power torsion induced by `φ : R →+* R'`. -/
@[stacks 0BNR "the map on power torsion"]
noncomputable def fPowerTorsionToExtension
    (φ : R →+* R') (f : R) :
    let _ : Algebra R R' := φ.toAlgebra
    Submodule.torsion' R R (Submonoid.powers f) →ₗ[R]
      Submodule.torsion' R R' (Submonoid.powers f) :=
  let _ : Algebra R R' := φ.toAlgebra
  ((Algebra.linearMap R R').domRestrict
      (Submodule.torsion' R R (Submonoid.powers f))).codRestrict
    (Submodule.torsion' R R' (Submonoid.powers f))
    (algebraMap_mem_fPowerTorsion φ f)

/-- The left map `R → R' × R_f` in the Beauville-Laszlo Cech sequence. -/
@[stacks 0BNR "the left map in the Cech sequence"]
abbrev beauvilleLaszloCechLeftMap
    (φ : R →+* R') (f : R) :
    let _ : Algebra R R' := φ.toAlgebra
    R →ₗ[R] R' × Localization.Away f :=
  let _ : Algebra R R' := φ.toAlgebra
  LinearMap.prod
    (Algebra.linearMap R R')
    (Algebra.linearMap R (Localization.Away f))

/-- The right map `R' × R_f → R'_f` in the Beauville-Laszlo Cech sequence. -/
@[stacks 0BNR "the right map in the Cech sequence"]
abbrev beauvilleLaszloCechRightMap
    (φ : R →+* R') (f : R) :
    let _ : Algebra R R' := φ.toAlgebra
    R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
  let _ : Algebra R R' := φ.toAlgebra
  let left : R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
    ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R).comp
      (LinearMap.fst R R' (Localization.Away f))
  let right : R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f) :=
    ((Localization.awayMapₐ (Algebra.ofId R R') f).toLinearMap).comp
      (LinearMap.snd R R' (Localization.Away f))
  left - right

/-- The two maps in the Beauville-Laszlo Cech sequence compose to zero. -/
@[stacks 0BNR, stacks 0BNQ "the Cech maps form a complex"]
theorem beauvilleLaszloCech_comp_eq_zero
    (φ : R →+* R') (f : R) :
    let _ : Algebra R R' := φ.toAlgebra
    (beauvilleLaszloCechRightMap φ f).comp (beauvilleLaszloCechLeftMap φ f) =
      (0 : R →ₗ[R] Localization.Away (algebraMap R R' f)) := sorry

/-- The canonical Beauville-Laszlo Cech short complex for `(φ, f)`. -/
@[stacks 0BNR, stacks 0F1Q "the Beauville-Laszlo Cech sequence"]
noncomputable def beauvilleLaszloCechSequence
    (φ : R →+* R') (f : R) :
    let _ : Algebra R R' := φ.toAlgebra
    ShortComplex (ModuleCat R) :=
  let _ : Algebra R R' := φ.toAlgebra
  ModuleCat.shortComplexOfCompEqZero
    (beauvilleLaszloCechLeftMap φ f)
    (beauvilleLaszloCechRightMap φ f)
    (beauvilleLaszloCech_comp_eq_zero φ f)

/-- A Beauville-Laszlo glueing pair consists of compatible positive-power quotients and a short
exact Beauville-Laszlo Cech sequence. -/
@[stacks 0BNR "Beauville-Laszlo glueing pair"]
class IsBeauvilleLaszloGlueingPairAlong
    (φ : R →+* R') (f : R) : Prop where
  /-- Every positive-power quotient comparison is bijective. -/
  quotientMapBijective :
    ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n)
  /-- The associated Beauville-Laszlo Cech sequence is short exact. -/
  shortExact :
    let _ : Algebra R R' := φ.toAlgebra
    (beauvilleLaszloCechSequence φ f).ShortExact

/-- Lemma 15.91.6 (1): positive-power quotient bijectivity makes the right Cech map
surjective. -/
@[stacks 0BNR "Lemma 15.91.6 (1)"]
theorem beauvilleLaszloCechRightMap_surjective_of_principalPowerQuotientMapBijective
    (φ : R →+* R') (f : R)
    (hquot : ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n)) :
    let _ : Algebra R R' := φ.toAlgebra
    Function.Surjective
      (beauvilleLaszloCechRightMap φ f :
        R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f)) := sorry

/-- Lemma 15.91.6 (2): under positive-power quotient bijectivity, left exactness is equivalent to
injectivity on `f`-power torsion. -/
@[stacks 0BNR "Lemma 15.91.6 (2)"]
theorem beauvilleLaszloCechLeftMap_injective_iff_fPowerTorsionToExtension_injective
    (φ : R →+* R') (f : R)
    (hquot : ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n)) :
    let _ : Algebra R R' := φ.toAlgebra
    Function.Injective
      (beauvilleLaszloCechLeftMap φ f : R →ₗ[R] R' × Localization.Away f) ↔
      Function.Injective (fPowerTorsionToExtension φ f) := sorry

/-- Lemma 15.91.6 (3): under positive-power quotient bijectivity, exactness in the middle is
equivalent to surjectivity on `f`-power torsion. -/
@[stacks 0BNR "Lemma 15.91.6 (3)"]
theorem beauvilleLaszloCechMiddle_exact_iff_fPowerTorsionToExtension_surjective
    (φ : R →+* R') (f : R)
    (hquot : ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n)) :
    let _ : Algebra R R' := φ.toAlgebra
    Function.Exact
      (beauvilleLaszloCechLeftMap φ f : R →ₗ[R] R' × Localization.Away f)
      (beauvilleLaszloCechRightMap φ f :
        R' × Localization.Away f →ₗ[R] Localization.Away (algebraMap R R' f)) ↔
      Function.Surjective (fPowerTorsionToExtension φ f) := sorry

/-- Lemma 15.91.6: under positive-power quotient bijectivity, the Beauville-Laszlo glueing-pair
condition is equivalent to bijectivity on `f`-power torsion. -/
@[stacks 0BNR "Lemma 15.91.6"]
theorem isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsionToExtension
    (φ : R →+* R') (f : R)
    (hquot : ∀ n : ℕ+, Function.Bijective (principalPowerIdealImageQuotientMap φ f n)) :
    let _ : Algebra R R' := φ.toAlgebra
    IsBeauvilleLaszloGlueingPairAlong φ f ↔
      Function.Bijective (fPowerTorsionToExtension φ f) := sorry

/-- Lemma 15.91.6 specialized to the `(f)`-adic completion. -/
@[stacks 0BNR "Lemma 15.91.6, completion specialization"]
theorem principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion
    {R : Type u} [CommRing R] (f : R) :
    IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f)) f ↔
      Function.Bijective
        (fPowerTorsionToExtension (algebraMap R (principalAdicCompletion f)) f) := sorry
