/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Noetherian DVR base change and residue fields

This leaf records the Noetherian and residue-field consequences of an algebraic reduced
tensor-product base change of an essentially finite type DVR extension.

@stack 09IH
-/

@[expose] public section

open scoped TensorProduct

open PrimeSpectrum

universe u v w x y

namespace DVR.BaseChange

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B] [Algebra.EssFiniteType A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [Algebra A L] [Algebra K L]
variable [IsFractionRing B L] [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [Algebra.IsAlgebraic K K1]

/-- Lemma 15.117.7 (1): if the source normalization is Noetherian, then the target
normalization in the reduced tensor-product base change is Noetherian. -/
@[stacks 09IH "(1), Noetherian target normalization"]
theorem targetNormalization_noetherian
    (hsource : IsNoetherianRing (integralClosure A K1)) :
    IsNoetherianRing
      (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)) := sorry
-- Proof strategy: install `hsource`, use essential finite type of the DVR map to show `L / K` is
-- finite-dimensional, and decompose the reduced tensor product with the algebraic extension `K1`
-- into its finite product of field branches.  On each branch, localize the source normalization
-- at its contracted prime and apply the one-dimensional Krull-Akizuki/finite-normalization theorem
-- to the induced finite fraction-field extension.  Transport Noetherianity across the branch
-- integral-closure equivalences and recombine the finite product to obtain the target
-- normalization result.

/-- Lemma 15.117.7 (3): residue fields along the normalization comparison are finitely generated
field extensions. -/
@[stacks 09IH "(3), finite type residue-field extension"]
theorem residueField_finiteType
    (hsource : IsNoetherianRing (integralClosure A K1))
    (q : PrimeSpectrum
      (integralClosure B (FieldExtension.TensorProduct.reduced K L K1))) :
    letI : Algebra
        (q.asIdeal.under (integralClosure A K1)).ResidueField
        q.asIdeal.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver
        (q.asIdeal.under (integralClosure A K1)) q.asIdeal
    Algebra.FiniteType
      (q.asIdeal.under (integralClosure A K1)).ResidueField
      q.asIdeal.ResidueField := sorry
-- Proof strategy: use `hsource` and place `q` on its unique field factor in the reduced generic
-- fiber decomposition.  If the contracted prime on the source normalization is zero, identify the
-- two residue fields with fraction fields and use algebraicity together with essential finite type
-- to get a finite extension.  Otherwise localize both normalizations at the contracted pair and
-- apply the finite-type residue-field theorem for a Noetherian one-dimensional integral extension.
-- Transport the resulting `Algebra.FiniteType` instance through
-- `Ideal.ResidueField.algebraOfLiesOver` and the canonical localization residue-field equivalences.

end DVR.BaseChange
