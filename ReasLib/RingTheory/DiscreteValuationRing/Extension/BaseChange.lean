/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.TensorProduct.Branch
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Integral-closure base change for DVR extensions

This module owns the canonical comparison map on the integral closures occurring in a reduced
tensor-product base change.  The reduced tensor product is a ring (not generally a field);
field and DVR structures enter only after a branch is selected.  The module is independent of the
Chapter 15 source files; the weak-solution predicates use this map as their branch algebra.

@stack 09EM
-/

open scoped TensorProduct

universe u v w x y z

-- Local instance justification (instance diamond): the tensor product exposes left and right
-- algebra actions with the same underlying scalar map; select the right action only while
-- constructing the canonical `A`-algebra map through the right tensor factor.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace integralClosure.BaseChange

section Core

variable {A : Type u} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A]
variable [Field K] [Algebra A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

/-- The canonical `A`-algebra map from `K₁` to the reduced tensor-product base change of `L`.
This is the right tensor-factor map followed by quotienting by the nilradical. -/
@[stacks 09EM "right tensor factor in a reduced tensor-product base change"]
abbrev rightFactor :
    K1 →ₐ[A] FieldExtension.TensorProduct.reduced K L K1 :=
  (Ideal.Quotient.mkₐ A _).comp
    ((Algebra.TensorProduct.includeRight : K1 →ₐ[K] L ⊗[K] K1).restrictScalars A)

/-- The induced map from the integral closure of `A` in `K₁` to the integral closure of `A` in
the reduced tensor-product base change. -/
@[stacks 09EM "integral-closure map into reduced base change"]
abbrev sourceMap :
    integralClosure A K1 →ₐ[A] FieldExtension.TensorProduct.reduced K L K1 :=
  (integralClosure A (FieldExtension.TensorProduct.reduced K L K1)).val.comp
    rightFactor.mapIntegralClosure

end Core

section RawReduced

variable {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing B]
variable [Field K] [Field L] [Field K1]
variable [Algebra B L] [Algebra K L] [Algebra K K1]

/-- The integral closures in the raw and reduced tensor products are canonically equivalent when
the finite base-change field is separable.  This is the normalization bridge used to move between
source-facing tensor products and the reduced branch model. -/
@[stacks 09EM "raw-to-reduced integral-closure equivalence", stacks 09EY
  "raw-to-reduced integral-closure equivalence"]
noncomputable def rawReducedEquiv [FiniteDimensional K K1] [Algebra.IsSeparable K K1] :
    integralClosure B (L ⊗[K] K1) ≃ₐ[B]
      integralClosure B (FieldExtension.TensorProduct.reduced K L K1) :=
  (AlgEquiv.restrictScalars B
    (FieldExtension.TensorProduct.tensorEquivReduced (K := K) (L := L) (K1 := K1))).mapIntegralClosure

/-- The raw-to-reduced integral-closure equivalence is induced by the canonical quotient on the
ambient tensor products. -/
@[simp, stacks 09EM "raw-to-reduced integral-closure application", stacks 09EY
  "raw-to-reduced integral-closure application"]
theorem coe_rawReducedEquiv_apply [FiniteDimensional K K1] [Algebra.IsSeparable K K1]
    (x : integralClosure B (L ⊗[K] K1)) :
    ((rawReducedEquiv (B := B) (K := K) (L := L) (K1 := K1) x :
        integralClosure B (FieldExtension.TensorProduct.reduced K L K1)) :
      FieldExtension.TensorProduct.reduced K L K1) =
      FieldExtension.TensorProduct.tensorEquivReduced (K := K) (L := L) (K1 := K1) x := sorry

end RawReduced

section RawTower

variable {B : Type u} {C : Type v} {K : Type w} {L : Type x} {M : Type y} {K1 : Type z}
variable [CommRing B] [CommRing C] [Algebra B C]
variable [Field K] [Field L] [Field M] [Field K1]
variable [Algebra B L] [Algebra B M] [Algebra C M]
variable [Algebra K L] [Algebra K M] [Algebra K K1] [Algebra L M]
variable [IsScalarTower B C M] [IsScalarTower B L M] [IsScalarTower K L M]

/-- The ambient map underlying the second raw integral-closure comparison. -/
@[stacks 09EY "ambient map for the raw integral-closure tower"]
def ambientTowerMap :
    integralClosure B (L ⊗[K] K1) →ₐ[B] M ⊗[K] K1 :=
  (integralClosure B (M ⊗[K] K1)).val.comp
    ((FieldExtension.TensorProduct.baseChangeMap
      (K := K) (L := L) (M := M) (K1 := K1)).restrictScalars B).mapIntegralClosure

/-- The ambient tower map sends integral elements over `B` to elements integral over `C`. -/
@[stacks 09EY "integrality for the raw integral-closure tower"]
theorem ambientTowerMap_mem (b : integralClosure B (L ⊗[K] K1)) :
    ambientTowerMap (B := B) (K := K) (L := L) (M := M) (K1 := K1) b ∈
      integralClosure C (M ⊗[K] K1) := sorry

/-- The canonical map from the integral closure of `B` in `L ⊗[K] K₁` to the integral
closure of `C` in `M ⊗[K] K₁`. -/
@[stacks 09EY "second map between raw integral closures"]
def towerMap :
    integralClosure B (L ⊗[K] K1) →ₐ[B] integralClosure C (M ⊗[K] K1) :=
  AlgHom.codRestrict
    (ambientTowerMap (B := B) (K := K) (L := L) (M := M) (K1 := K1))
    ((integralClosure C (M ⊗[K] K1)).restrictScalars B)
    (ambientTowerMap_mem (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1))

/-- The second raw comparison map agrees with the tensor-product base-change map on ambient
elements. -/
@[simp, stacks 09EY "second raw integral-closure comparison application"]
theorem coe_towerMap_apply (b : integralClosure B (L ⊗[K] K1)) :
    (towerMap (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) b :
        M ⊗[K] K1) =
      FieldExtension.TensorProduct.baseChangeMap
        (K := K) (L := L) (M := M) (K1 := K1) b := sorry

/-- The canonical, non-instance algebra structure induced by `towerMap`. -/
@[implicit_reducible, stacks 09EY "algebra structure for the raw integral-closure tower"]
def towerAlgebra :
    Algebra (integralClosure B (L ⊗[K] K1)) (integralClosure C (M ⊗[K] K1)) :=
  (towerMap (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1)).toRingHom.toAlgebra

end RawTower

section Comparison

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Field K] [Algebra A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

/-- Elements of the source integral closure map into the target integral closure over `B`. -/
@[stacks 09EM "integrality of the base-change comparison map"]
theorem sourceMap_mem
    (x : integralClosure A K1) :
    sourceMap (A := A) (K := K) (L := L) (K1 := K1) x ∈
      integralClosure B (FieldExtension.TensorProduct.reduced K L K1) := sorry

/-- The canonical comparison map between the two integral closures in a reduced
tensor-product base change.  Its codomain is bundled, so downstream branch constructions can use
typeclass search directly. -/
@[stacks 09EM "integral-closure comparison map for a reduced tensor-product base change"]
def map :
    integralClosure A K1 →ₐ[A] integralClosure B (FieldExtension.TensorProduct.reduced K L K1) :=
  AlgHom.codRestrict
    (sourceMap (A := A) (K := K) (L := L) (K1 := K1))
    ((integralClosure B (FieldExtension.TensorProduct.reduced K L K1)).restrictScalars A)
    (sourceMap_mem
      (A := A) (B := B) (K := K) (L := L) (K1 := K1))

/-- The comparison map supplies the canonical algebra structure on the target integral closure. -/
@[stacks 09EM "algebra structure on the target integral closure"]
instance algebra :
    Algebra (integralClosure A K1)
      (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)) :=
  (map (A := A) (B := B) (K := K) (L := L) (K1 := K1)).toRingHom.toAlgebra

/-- Remark 15.115.1 (09EM): applying the bundled comparison map agrees with its underlying
integral-closure map into the reduced tensor-product algebra. -/
@[simp, stacks 09EM "comparison map application"]
theorem map_apply
    (x : integralClosure A K1) :
    (map (A := A) (B := B) (K := K) (L := L) (K1 := K1) x :
      FieldExtension.TensorProduct.reduced K L K1) =
      sourceMap (A := A) (K := K) (L := L) (K1 := K1) x := sorry

end Comparison

section RawComparison

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Field K] [Algebra A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

/-- The right tensor-factor map from `K₁` to the raw tensor product, viewed over `A`. -/
@[stacks 09EY "right tensor factor in a raw tensor-product base change"]
abbrev rawRightFactor : K1 →ₐ[A] L ⊗[K] K1 :=
  (Algebra.TensorProduct.includeRight : K1 →ₐ[K] L ⊗[K] K1).restrictScalars A

/-- The ambient map from the source integral closure to the raw tensor product. -/
@[stacks 09EY "ambient source map into a raw tensor-product base change"]
abbrev rawAmbientMap : integralClosure A K1 →ₐ[A] L ⊗[K] K1 :=
  (integralClosure A (L ⊗[K] K1)).val.comp rawRightFactor.mapIntegralClosure

/-- Elements of the source integral closure map into the raw integral closure over `B`. -/
@[stacks 09EY "integrality of the raw base-change comparison map"]
theorem rawAmbientMap_mem (a : integralClosure A K1) :
    rawAmbientMap (A := A) (K := K) (L := L) (K1 := K1) a ∈
      integralClosure B (L ⊗[K] K1) := sorry

/-- The canonical map from the source normalization to the integral closure in the raw tensor
product.  Its function is induced directly by the right tensor-factor inclusion. -/
@[stacks 09EY "source map between raw integral closures"]
def rawMap : integralClosure A K1 →ₐ[A] integralClosure B (L ⊗[K] K1) :=
  AlgHom.codRestrict
    (rawAmbientMap (A := A) (K := K) (L := L) (K1 := K1))
    ((integralClosure B (L ⊗[K] K1)).restrictScalars A)
    (rawAmbientMap_mem (A := A) (B := B) (K := K) (L := L) (K1 := K1))

/-- The raw comparison map agrees with the right tensor-factor map on ambient elements. -/
@[simp, stacks 09EY "raw integral-closure comparison application"]
theorem coe_rawMap_apply (a : integralClosure A K1) :
    ((rawMap (A := A) (B := B) (K := K) (L := L) (K1 := K1) a :
        integralClosure B (L ⊗[K] K1)) : L ⊗[K] K1) =
      rawRightFactor (A := A) (K := K) (L := L) (K1 := K1) a := sorry

/-- The canonical, non-instance algebra structure induced by `rawMap`.  Keeping it explicit avoids
competing with algebra structures transported through the reduced tensor product. -/
@[implicit_reducible, stacks 09EY "algebra structure between raw integral closures"]
def rawAlgebra :
    Algebra (integralClosure A K1) (integralClosure B (L ⊗[K] K1)) :=
  (rawMap (A := A) (B := B) (K := K) (L := L) (K1 := K1)).toRingHom.toAlgebra

end RawComparison

end integralClosure.BaseChange

namespace DVR.BaseChange

/-- A branch of a reduced tensor-product base change consists of a maximal ideal in each
normalization, with the target ideal lying over the source ideal.  Bundling the pair keeps the
ambient algebra/tower context in the type; finiteness hypotheses remain explicit external
instances. -/
@[stacks 09EM "maximal branch of a DVR tensor-product base change"]
structure Branch
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (K1 : Type y)
    [CommRing A] [CommRing B] [Algebra A B]
    [Field K] [Algebra A K]
    [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1] where
  /-- The selected maximal ideal of the source normalization. -/
  source : MaximalSpectrum (integralClosure A K1)
  /-- The selected maximal ideal of the target normalization. -/
  target : MaximalSpectrum
    (integralClosure B (FieldExtension.TensorProduct.reduced K L K1))
  /-- The target branch lies over the source branch for the canonical normalization map. -/
  liesOver : target.asIdeal.LiesOver source.asIdeal

namespace Branch

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Field K] [Algebra A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

/-- Two bundled base-change branches are equal when their selected source and target points agree. -/
@[ext, stacks 09EM "extensionality for a base-change branch"]
theorem ext {b b' : Branch A B K L K1}
    (hsource : b.source = b'.source) (htarget : b.target = b'.target) : b = b' := sorry

/-- Construct a bundled base-change branch from a pair of maximal ideals and a lying-over
instance. -/
@[stacks 09EM "base-change branch from maximal ideals"]
def ofIdeals
    (p : Ideal (integralClosure A K1)) [p.IsMaximal]
    (q : Ideal (integralClosure B (FieldExtension.TensorProduct.reduced K L K1))) [q.IsMaximal]
    [hqp : q.LiesOver p] :
    Branch A B K L K1 where
  source := ⟨p, inferInstance⟩
  target := ⟨q, inferInstance⟩
  liesOver := hqp

end Branch

end DVR.BaseChange

namespace DVR.BaseChange

section Spectrum

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

/-- The canonical comparison of integral closures is surjective on spectra for a DVR extension.
This is the reusable 09EM owner; finite-dimensionality of `K₁ / K` is deliberately not required for
the spectral lifting statement. -/
@[stacks 09EM "spectrum surjectivity for reduced tensor-product base change",
  stacks 09IH "Lemma 15.117.7 (2), spectrum surjectivity"]
theorem spectrum_comap_surjective :
    Function.Surjective
      (PrimeSpectrum.comap
        (algebraMap (integralClosure A K1)
          (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)))) := sorry

end Spectrum

end DVR.BaseChange
