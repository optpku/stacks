/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.BasicOpen.Closure
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- The finite union of principal opens, its localization-product map, and its kernel ideal. -/
#check
  (AlgebraicGeometry.Spec.BasicOpenUnion.union :
    ∀ {A : Type u} [CommRing A] {n : ℕ}, (Fin n → A) →
      (AlgebraicGeometry.Spec (CommRingCat.of A)).Opens)

#check
  (AlgebraicGeometry.Spec.BasicOpenUnion.localizationProductMap :
    ∀ {A : Type u} [CommRing A] {n : ℕ} (f : Fin n → A),
      A →+* (∀ i : Fin n, Localization.Away (f i)))

#check
  (AlgebraicGeometry.Spec.BasicOpenUnion.closureIdeal :
    ∀ {A : Type u} [CommRing A] {n : ℕ}, (Fin n → A) → Ideal A)

/- Example 29.7.4: the canonical isomorphism from the scheme-theoretic closure of the finite
union of principal opens to the quotient spectrum commutes with their closed immersions into
the affine spectrum. -/
@[stacks 056C] #check
  (AlgebraicGeometry.Spec.BasicOpenUnion.schemeTheoreticClosureIso_hom_comp_quotientMap :
    ∀ {A : Type u} [CommRing A] {n : ℕ} (f : Fin n → A),
      (AlgebraicGeometry.Spec.BasicOpenUnion.schemeTheoreticClosureIso f).hom ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (AlgebraicGeometry.Spec.BasicOpenUnion.closureIdeal f))) =
        AlgebraicGeometry.schemeTheoreticClosureι
          (AlgebraicGeometry.Spec.BasicOpenUnion.union f))

/- The inclusion of the finite union of principal opens is quasi-compact. -/
#check
  (AlgebraicGeometry.Spec.BasicOpenUnion.quasiCompact_ι :
    ∀ {A : Type u} [CommRing A] {n : ℕ} (f : Fin n → A),
      AlgebraicGeometry.QuasiCompact
        (AlgebraicGeometry.Spec.BasicOpenUnion.union f).ι)

/- The finite union is scheme-theoretically dense exactly when its localization-product kernel
is the zero ideal. -/
#check
  (AlgebraicGeometry.Spec.BasicOpenUnion.schemeTheoreticallyDense_iff_closureIdeal_eq_bot :
    ∀ {A : Type u} [CommRing A] {n : ℕ} (f : Fin n → A),
      AlgebraicGeometry.schemeTheoreticallyDense
          (AlgebraicGeometry.Spec.BasicOpenUnion.union f) ↔
        AlgebraicGeometry.Spec.BasicOpenUnion.closureIdeal f = ⊥)
