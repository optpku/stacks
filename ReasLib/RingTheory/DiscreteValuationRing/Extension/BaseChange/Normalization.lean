/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.IntegralClosure
public import ReasLib.RingTheory.Henselian.IntegralClosure.PrimeFiber
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import ReasLib.RingTheory.LocalRing.Product
public import ReasLib.RingTheory.Normal.Nagata
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Normalization consequences of DVR base change

This module owns the finite, Henselian, purely inseparable, separable, and Nagata consequences of
the integral-closure comparison map.  The reduced tensor product is kept as a ring; a field or DVR
appears only after the corresponding branch or factor is selected.

@stack 09EM
-/

open Ideal IsLocalRing
open scoped TensorProduct

universe u v w x y z

namespace integralClosure.BaseChange

section TensorComparison

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Field K] [Algebra A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

/-- Remark 15.115.1: the source-order tensor comparison map into the target integral closure. -/
@[stacks 09EM "tensor-to-integral-closure comparison map"]
noncomputable def tensorMap :
    B ⊗[A] integralClosure A K1 →ₐ[A]
      integralClosure B (FieldExtension.TensorProduct.reduced K L K1) :=
  ((IsScalarTower.toAlgHom A B
      (integralClosure B (FieldExtension.TensorProduct.reduced K L K1))).liftEquiv
      A (integralClosure A K1) B
      (integralClosure B (FieldExtension.TensorProduct.reduced K L K1))).restrictScalars A |>.comp
    (Algebra.TensorProduct.comm A B (integralClosure A K1)).toAlgHom

/-- Remark 15.115.1: the tensor comparison map on a pure tensor. -/
@[stacks 09EM "tensor comparison on pure tensors"]
theorem tensorMap_tmul (b : B) (a : integralClosure A K1) :
    tensorMap (A := A) (B := B) (K := K) (L := L) (K1 := K1) (TensorProduct.tmul A b a) =
      algebraMap B (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)) b *
        integralClosure.BaseChange.map (A := A) (B := B) (K := K) (L := L) (K1 := K1) a := sorry
-- Proof strategy: unfold `tensorMap`, evaluate `Algebra.TensorProduct.comm` on the pure tensor,
-- apply the defining rule for `IsScalarTower.toAlgHom.liftEquiv`, and finish with
-- `integralClosure.BaseChange.map_apply` on the right factor.

end TensorComparison

section FactorComparison

variable {B : Type u} {C : Type v} {L : Type w} {M : Type x} {F : Type y}
variable [CommRing B] [CommRing C] [Algebra B C]
variable [Field L] [Algebra B L]
variable [Field M] [Algebra B M] [Algebra C M] [Algebra L M]
variable [IsScalarTower B C M] [IsScalarTower B L M]
variable [Field F] [Algebra B F] [Algebra L F] [IsScalarTower B L F]

/-- The canonical normalized map for a selected tensor-product factor.  It is obtained by including
the normalized `B`-algebra on the right tensor factor and applying the comparison map for
`B ⟶ C`; the target is the integral closure of `C` in the reduced `M ⊗[L] F`. -/
@[stacks 09ES "normalized factor comparison map", stacks 09EY
  "normalized factor comparison map"]
noncomputable def factorMap :
    integralClosure B F →ₐ[B]
      integralClosure C (FieldExtension.TensorProduct.reduced L M F) :=
  (tensorMap (A := B) (B := C) (K := L) (L := M) (K1 := F)).comp
    Algebra.TensorProduct.includeRight

/-- Applying the normalized factor map is the same as first including the right tensor factor and
then applying the comparison map. -/
@[simp, stacks 09ES "normalized factor comparison application", stacks 09EY
  "normalized factor comparison application"]
theorem factorMap_apply (x : integralClosure B F) :
    (factorMap (B := B) (C := C) (L := L) (M := M) (F := F) x :
        FieldExtension.TensorProduct.reduced L M F) =
      tensorMap (A := B) (B := C) (K := L) (L := M) (K1 := F)
        (Algebra.TensorProduct.includeRight x) := sorry
-- Proof strategy: unfold `factorMap`, rewrite `AlgHom.comp_apply`, and use the right-factor
-- specialization of `tensorMap_tmul`; coercion to the reduced tensor product removes the
-- integral-closure subtype wrapper.

end FactorComparison

end integralClosure.BaseChange

namespace DVR.BaseChange

section FactorBranch

variable {B : Type u} {C : Type v} {K : Type w} {L : Type x} {M : Type y} {K1 : Type z}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra B C] [IsExtensionOfDiscreteValuationRings B C]
variable [Field K] [Field L] [Algebra K L]
variable [Field M] [Algebra B L] [Algebra B M] [Algebra C M] [Algebra L M]
variable [IsFractionRing B L] [IsFractionRing C M]
variable [IsScalarTower B C M] [IsScalarTower B L M]
variable [Field K1] [Algebra K K1] [FiniteDimensional K K1]

/-- The canonical map on the integral closures selected by a maximal reduced-tensor branch.  The
quotient field and its two scalar actions are installed only for this map, so no branch-dependent
algebra becomes a global instance. -/
@[stacks 09ES "branchwise normalized comparison map", stacks 09EY
  "branchwise normalized comparison map"]
noncomputable def branchMap
    (m : MaximalSpectrum (FieldExtension.TensorProduct.reduced K L K1)) :
    let F := FieldExtension.TensorProduct.reduced K L K1 ⧸ m.asIdeal
    -- Local instance justification (defeq pin): use the field structure attached to this maximal
    -- quotient before exposing the reduced tensor target.
    let _ : Field F := Ideal.Quotient.field m.asIdeal
    -- Local instance justification (instance diamond): choose the quotient's canonical scalar
    -- actions only for this branch map.
    let _ : Algebra B F := inferInstance
    let _ : Algebra L F := inferInstance
    -- Local instance justification (proof-local temporary data): expose the scalar tower needed
    -- by the integral-closure comparison map without exporting it to other branches.
    let _ : IsScalarTower B L F := inferInstance
    integralClosure B F →ₐ[B] integralClosure C
      (FieldExtension.TensorProduct.reduced L M F) :=
  let F := FieldExtension.TensorProduct.reduced K L K1 ⧸ m.asIdeal
  -- Local instance justification (defeq pin): use the field structure attached to this maximal
  -- quotient while constructing the map.
  let _ : Field F := Ideal.Quotient.field m.asIdeal
  -- Local instance justification (instance diamond): choose the quotient's canonical scalar
  -- actions only for this branch map.
  let _ : Algebra B F := inferInstance
  let _ : Algebra L F := inferInstance
  -- Local instance justification (proof-local temporary data): expose the scalar tower needed by
  -- the integral-closure comparison map without exporting it to other branches.
  let _ : IsScalarTower B L F := inferInstance
  integralClosure.BaseChange.factorMap

/-- The branch map is the generic normalized factor map for the quotient field selected by `m`. -/
@[simp, stacks 09ES "branchwise normalized comparison application", stacks 09EY
  "branchwise normalized comparison application"]
theorem branchMap_apply
    (m : MaximalSpectrum (FieldExtension.TensorProduct.reduced K L K1)) :
    let F := FieldExtension.TensorProduct.reduced K L K1 ⧸ m.asIdeal
    -- Local instance justification (defeq pin): use the field structure attached to this maximal
    -- quotient while stating the application law.
    let _ : Field F := Ideal.Quotient.field m.asIdeal
    -- Local instance justification (instance diamond): choose the quotient's canonical scalar
    -- actions only for this branch application law.
    let _ : Algebra B F := inferInstance
    let _ : Algebra L F := inferInstance
    -- Local instance justification (proof-local temporary data): expose the scalar tower needed
    -- by the comparison map only in this statement.
    let _ : IsScalarTower B L F := inferInstance
    ∀ x : integralClosure B F,
      (branchMap (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) m x :
          FieldExtension.TensorProduct.reduced L M F) =
        integralClosure.BaseChange.tensorMap (A := B) (B := C) (K := L) (L := M) (K1 := F)
          (Algebra.TensorProduct.includeRight x) := sorry
-- Proof strategy: unfold `branchMap` under the displayed quotient-field and scalar-tower pins,
-- then apply `integralClosure.BaseChange.factorMap_apply` for the selected maximal factor.

end FactorBranch

section DVRComparison

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

/-- Remark 15.115.1: the tensor comparison map is integral. -/
@[stacks 09EM "integrality of the tensor comparison map"]
theorem tensorMap_isIntegral :
    (integralClosure.BaseChange.tensorMap (A := A) (B := B) (K := K) (L := L) (K1 := K1)).toRingHom.IsIntegral := sorry
-- Proof strategy: view the target integral closure as integral over `B`, install the algebra tower
-- `B -> B ⊗[A] integralClosure A K1 -> integralClosure B (reduced K L K1)`, and apply
-- `IsIntegral.tower_top` elementwise through the explicit tensor comparison map.

/-- Remark 15.115.1: every element of the tensor comparison kernel is nilpotent. -/
@[stacks 09EM "locally nilpotent kernel of the tensor comparison map"]
theorem tensorMap_kernel_isLocallyNilpotent :
    (RingHom.ker
      (integralClosure.BaseChange.tensorMap
        (A := A) (B := B) (K := K) (L := L) (K1 := K1)).toRingHom).IsLocallyNilpotent := sorry
-- Proof strategy: compose the tensor comparison with the inclusion into the reduced generic
-- fiber.  A kernel element maps into the nilradical of the raw tensor product, and injectivity of
-- the raw generic-fiber tensor map pulls its nilpotence back to the source.

/-- For finite base change, the locally nilpotent tensor comparison kernel is a nilpotent ideal. -/
@[stacks 09EM "nilpotent kernel for finite tensor base change"]
theorem tensorMap_kernel_isNilpotent [FiniteDimensional K K1] :
    IsNilpotent (RingHom.ker
      (integralClosure.BaseChange.tensorMap (A := A) (B := B) (K := K) (L := L) (K1 := K1)).toRingHom) := sorry
-- Proof strategy: compare the map with the raw generic-fiber tensor map, identify vanishing after
-- reduction with `tensorMap_kernel_isLocallyNilpotent`.  Finite-dimensionality makes the source
-- tensor algebra Noetherian, so the finitely generated kernel is nilpotent by
-- `Ideal.FG.isNilpotent_of_le_locallyNilpotent`.

end DVRComparison

section SourceFinite

variable {A : Type u} {K : Type w} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

/-- Remark 15.115.1: finite base change makes the source normalization Dedekind. -/
@[stacks 09EM "Dedekind source normalization"]
theorem sourceIsDedekindDomain [FiniteDimensional K K1] :
    IsDedekindDomain (integralClosure A K1) := sorry
-- Proof strategy: compare the chosen fraction field `K` with `FractionRing A`, transport
-- finite-dimensionality to the canonical fraction-ring action, and apply
-- `integralClosure.isDedekindDomain` to the finite extension.

/-- Remark 15.115.1: a finite separable base change makes the source normalization finite. -/
@[stacks 09EM "finite separable source normalization"]
theorem sourceModuleFinite_of_finiteSeparable [FiniteDimensional K K1]
    [Algebra.IsSeparable K K1] :
    Module.Finite A (integralClosure A K1) := sorry
-- Proof strategy: transport the `K`-action to `FractionRing A` and apply
-- `integralClosure.moduleFinite_of_fractionField`, using finite-dimensionality and separability.

/-- Remark 15.115.1: a Nagata source has finite normalization after finite base change. -/
@[stacks 09EM "Nagata source normalization"]
theorem sourceModuleFinite_of_nagata [FiniteDimensional K K1] [NagataRing A] :
    Module.Finite A (integralClosure A K1) := sorry
-- Proof strategy: derive `IsN2Ring A` from `NagataRing A`, transport the finite extension from
-- `K` to `FractionRing A`, and apply `IsN2Ring.integralClosure_finite_of_finiteDimensional`.

/-- Remark 15.115.1: a finite purely inseparable base change preserves the source DVR. -/
@[stacks 09EM "purely inseparable source DVR"]
theorem sourceIsDVR_of_finitePurelyInseparable [FiniteDimensional K K1]
    [IsPurelyInseparable K K1] :
    ∃ hA1 : IsDomain (integralClosure A K1),
      @IsDiscreteValuationRing (integralClosure A K1) inferInstance hA1 := sorry
-- Proof strategy: use pure inseparability to show the integral closure is a valuation ring with
-- fraction field `K1`; combine this with the finite-extension Noetherian/Dedekind property and
-- package the resulting domain and DVR instances as the requested witnesses.

end SourceFinite

section TargetFinite

variable {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Field K] [Field L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [Field K1] [Algebra K K1] [FiniteDimensional K K1]

/-- Remark 15.115.1: finite base change makes the target normalization Dedekind. -/
@[stacks 09EM "Dedekind target normalization"]
theorem targetIsDedekindRing :
    IsDedekindRing (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)) := sorry
-- Proof strategy: use `FieldExtension.TensorProduct.reduced_finiteProductOfFields`, identify the
-- target integral closure factorwise, apply `IsIntegralClosure.isDedekindDomain` to every finite
-- field factor, and transport the product result to `IsDedekindRing`.

/-- Remark 15.115.1: the target normalization is a nonempty finite product of Dedekind domains. -/
@[stacks 09EM "finite product of target Dedekind domains"]
theorem targetFiniteProductOfDedekindDomains :
    ∃ D : RingProduct.Decomposition.Finite
        (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)),
      Nonempty D.index ∧ ∀ i, IsDedekindDomain (D.factor i) := sorry
-- Proof strategy: refine the finite field-factor decomposition of the reduced tensor product by
-- taking the integral closure of `B` in each factor, then assemble the factorwise algebra
-- equivalences with `RingProduct.Decomposition.Finite.ofAlgEquiv`.

/-- Remark 15.115.1: every maximal target localization is a DVR. -/
@[stacks 09EM "target localization DVR"]
theorem targetLocalizationIsDVR
    (q : Ideal (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)))
    [q.IsMaximal] :
    ∃ hq : IsDomain (Localization.AtPrime q),
      @IsDiscreteValuationRing (Localization.AtPrime q) inferInstance hq := sorry
-- Proof strategy: transport `q` through `targetFiniteProductOfDedekindDomains` to its unique
-- Dedekind-domain factor and use
-- `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`; return the induced domain
-- instance together with the DVR structure.

/-- Remark 15.115.1: a finite separable base change makes the target normalization finite. -/
@[stacks 09EM "finite separable target normalization"]
theorem targetModuleFinite_of_finiteSeparable [Algebra.IsSeparable K K1] :
    Module.Finite B (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)) := sorry
-- Proof strategy: use `reduced_finiteProductOfSeparableFields`; each factor integral closure is
-- finite over `B` by `IsIntegralClosure.finite`, and finite products preserve module finiteness.

/-- Remark 15.115.1: a Nagata target has finite normalization after finite base change. -/
@[stacks 09EM "Nagata target normalization"]
theorem targetModuleFinite_of_nagata [NagataRing B] :
    Module.Finite B (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)) := sorry
-- Proof strategy: decompose the reduced tensor product into its finite field factors, apply the
-- `IsN2Ring` consequence of `NagataRing B` to each finite factor, and transport module finiteness
-- across the finite-product normalization equivalence.

/-- Remark 15.115.1: a finite purely inseparable base change preserves the target DVR. -/
@[stacks 09EM "purely inseparable target DVR"]
theorem targetIsDVR_of_finitePurelyInseparable [IsPurelyInseparable K K1] :
    ∃ hB1 : IsDomain (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)),
      @IsDiscreteValuationRing
        (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)) inferInstance hB1 := sorry
-- Proof strategy: show that reduced base change by the finite purely inseparable extension has a
-- single field factor, identify the target with the corresponding integral closure, and combine
-- its valuation-ring and finite Noetherian properties to construct the domain and DVR witnesses.

end TargetFinite

section Henselian

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

/-- Remark 15.115.1: Henselianity of the source gives a DVR source normalization. -/
@[stacks 09EM "Henselian source normalization DVR"]
theorem sourceIsDVR_of_henselian [FiniteDimensional K K1] [HenselianLocalRing A] :
    IsDiscreteValuationRing (integralClosure A K1) := sorry
-- Proof strategy: use the canonical Henselian-local structure on the integral closure together
-- with `sourceIsDedekindDomain`; a local Dedekind domain that is not a field is a DVR by the
-- localization-at-its-maximal-ideal characterization.

/-- Remark 15.115.1: Henselianity of the target gives a unique branch over each source point. -/
@[stacks 09EM "Henselian target branch uniqueness"]
theorem targetExistsUnique_of_henselian [FiniteDimensional K K1] [HenselianLocalRing B]
    (p : Ideal (integralClosure A K1)) [p.IsMaximal] :
    ∃! q : Ideal (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)),
      q.IsMaximal ∧ q.LiesOver p := sorry
-- Proof strategy: obtain existence from `DVR.BaseChange.spectrum_comap_surjective`; decompose the
-- reduced generic fiber into field factors, apply
-- `integralClosure.Henselian.primesOver_eq_singleton` in the selected factor, and transport the
-- resulting uniqueness through the target normalization product equivalence.

end Henselian
