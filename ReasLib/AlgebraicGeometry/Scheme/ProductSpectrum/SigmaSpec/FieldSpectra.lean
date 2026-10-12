/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProductSpectrum.SigmaSpec
public import ReasLib.AlgebraicGeometry.Scheme.ProductSpectrum.FieldSpectra
public import ReasLib.AlgebraicGeometry.Scheme.Coproduct.FieldSpectra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Field-spectrum subobjects under the finite `sigmaSpec` comparison

This narrow bridge keeps the generic product-spectrum comparison independent of the
field-specific classifier while giving downstream arguments a single support/order transport API.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ProductSpectrum.FieldSpectra

/-- In the finite same-universe case, sigma-spectrum transport commutes with the two
field-spectrum subobject classifiers. -/
@[simp, stacks 03DP "field-spectrum subobject classifier under sigmaSpec"]
theorem subobjectEquivSet_sigmaSpec {ι : Type u} [Finite ι]
    (k : ι → Type u) [∀ i, Field (k i)]
    (P : Subobject (Coproduct.FieldSpectra.family k)) :
    subobjectEquivSet k
        ((ProductSpectrum.subobjectOrderIso
          (fun i ↦ CommRingCat.of (k i))) P) =
      Coproduct.FieldSpectra.subobjectEquivSet k P := sorry

/-- The same finite sigma-spectrum transport, stated directly for the support predicates. -/
@[simp, stacks 03DP "field-spectrum support under sigmaSpec"]
theorem subobjectSupport_sigmaSpec {ι : Type u} [Finite ι]
    (k : ι → Type u) [∀ i, Field (k i)]
    (P : Subobject (Coproduct.FieldSpectra.family k)) :
    subobjectSupport k
        ((ProductSpectrum.subobjectOrderIso
          (fun i ↦ CommRingCat.of (k i))) P) =
      Coproduct.FieldSpectra.subobjectSupport k P := sorry

/- The inverse transport is exposed explicitly so downstream users can start with the product
subobject classifier without spelling out `OrderIso.apply_symm_apply`. -/
/-- The inverse finite sigma-spectrum transport commutes with the two field-spectrum subobject
classifiers. -/
@[simp, stacks 03DP "inverse field-spectrum subobject classifier under sigmaSpec"]
theorem subobjectEquivSet_sigmaSpec_symm {ι : Type u} [Finite ι]
    (k : ι → Type u) [∀ i, Field (k i)]
    (Q : Subobject (ProductSpectrum.FieldSpectra.family k)) :
    Coproduct.FieldSpectra.subobjectEquivSet k
        ((ProductSpectrum.subobjectOrderIso
          (fun i ↦ CommRingCat.of (k i))).symm Q) =
      ProductSpectrum.FieldSpectra.subobjectEquivSet k Q := sorry

/-- The inverse support bridge for finite sigma-spectrum transport. -/
@[simp, stacks 03DP "inverse field-spectrum support under sigmaSpec"]
theorem subobjectSupport_sigmaSpec_symm {ι : Type u} [Finite ι]
    (k : ι → Type u) [∀ i, Field (k i)]
    (Q : Subobject (ProductSpectrum.FieldSpectra.family k)) :
    Coproduct.FieldSpectra.subobjectSupport k
        ((ProductSpectrum.subobjectOrderIso
          (fun i ↦ CommRingCat.of (k i))).symm Q) =
      ProductSpectrum.FieldSpectra.subobjectSupport k Q := sorry

end AlgebraicGeometry.Scheme.ProductSpectrum.FieldSpectra
