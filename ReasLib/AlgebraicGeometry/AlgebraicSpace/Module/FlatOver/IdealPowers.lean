/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldPoints

/-!
# Infinitesimal flatness over a Noetherian affine base

A coherent module on an algebraic space locally of finite presentation over a
Noetherian affine base is relatively flat above `V(I)` if its pullback to every
positive ideal-power thickening is relatively flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization (toBase)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {A : Type u} [CommRing A]

/-- The infinitesimal neighbourhood `Spec(A ⧸ I ^ n)`, as an algebraic space over
`Spec A`. -/
def idealPowerSpace (I : Ideal A) (n : ℕ) :
    AlgebraicSpace (Spec (CommRingCat.of A)) :=
  ofOver (Over.mk (Spec.quotientMap (R := CommRingCat.of A) (I ^ n)))

/-- The infinitesimal neighbourhood is represented by the affine quotient closed immersion. -/
theorem idealPowerSpace_eq (I : Ideal A) (n : ℕ) :
    idealPowerSpace I n =
      ofOver (Over.mk (Spec.quotientMap (R := CommRingCat.of A) (I ^ n))) :=
  rfl

/-- The canonical inclusion of `Spec(A ⧸ I ^ n)` into the base algebraic space. -/
def idealPowerι (I : Ideal A) (n : ℕ) :
    idealPowerSpace I n ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))) :=
  ofOverHomMk (Spec.quotientMap (R := CommRingCat.of A) (I ^ n))
    (Category.comp_id (Spec.quotientMap (R := CommRingCat.of A) (I ^ n)))

/-- The infinitesimal inclusion is the algebraic-space morphism induced by the quotient map. -/
theorem idealPowerι_eq (I : Ideal A) (n : ℕ) :
    idealPowerι I n =
      ofOverHomMk (Spec.quotientMap (R := CommRingCat.of A) (I ^ n))
        (Category.comp_id (Spec.quotientMap (R := CommRingCat.of A) (I ^ n))) :=
  rfl

/-- The infinitesimal fibre `Spec(A ⧸ I ^ n) ×_Spec A X`. -/
def idealPowerFiber (I : Ideal A) (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (n : ℕ) : AlgebraicSpace (Spec (CommRingCat.of A)) :=
  Limits.pullback (idealPowerι I n) (toBase X)

/-- The infinitesimal fibre is the chosen pullback of the infinitesimal inclusion and
the structural morphism. -/
theorem idealPowerFiber_eq (I : Ideal A)
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) (n : ℕ) :
    idealPowerFiber I X n = Limits.pullback (idealPowerι I n) (toBase X) :=
  rfl

/-- The pullback of an `𝒪_X`-module to the infinitesimal fibre. -/
def pullbackIdealPower (I : Ideal A) {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (F : X.Modules) (n : ℕ) : (idealPowerFiber I X n).Modules :=
  (pullback (Limits.pullback.snd (idealPowerι I n) (toBase X))).obj F

/-- Pullback to the infinitesimal fibre is module pullback along its second projection. -/
theorem pullbackIdealPower_eq (I : Ideal A)
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} (F : X.Modules) (n : ℕ) :
    pullbackIdealPower I F n =
      (pullback (Limits.pullback.snd (idealPowerι I n) (toBase X))).obj F :=
  rfl

/-- Over a Noetherian affine base, the relative-flatness locus of a coherent module on
a locally finitely presented algebraic space contains the inverse image of `V(I)` if
every positive ideal-power pullback is flat over the corresponding quotient spectrum. -/
@[stacks 08VP]
theorem zeroLocus_preimage_subset_flatOverLocus [IsNoetherianRing A] (I : Ideal A)
    (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    [LocallyOfFinitePresentation (toBase X)] (F : X.Modules) [F.IsCoherent]
    (hflat : ∀ n, 1 ≤ n →
      flatOver (pullbackIdealPower I F n)
        (Limits.pullback.fst (idealPowerι I n) (toBase X))) :
    Points.base ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ⊆
      flatOverLocus F (toBase X) :=
  sorry

/-- If each positive infinitesimal pullback of a coherent module on a locally finitely
presented algebraic space over a Noetherian affine base is relatively flat, then the
module is relatively flat at every point over `V(I)`. -/
theorem flatOverAt_of_mem_zeroLocus [IsNoetherianRing A] (I : Ideal A)
    (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    [LocallyOfFinitePresentation (toBase X)] (F : X.Modules) [F.IsCoherent]
    (hflat : ∀ n, 1 ≤ n →
      flatOver (pullbackIdealPower I F n)
        (Limits.pullback.fst (idealPowerι I n) (toBase X)))
    {x : Points X} (hx : Points.base x ∈ PrimeSpectrum.zeroLocus (I : Set A)) :
    flatOverAt F (toBase X) x :=
  zeroLocus_preimage_subset_flatOverLocus I X F hflat hx

end AlgebraicGeometry.AlgebraicSpace.Modules
