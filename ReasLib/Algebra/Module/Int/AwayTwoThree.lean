/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct

namespace Int

/-- The product of the localizations of `ℤ` away from `2` and `3`. -/
abbrev AwayTwoThree := Localization.Away (2 : ℤ) × Localization.Away (3 : ℤ)

namespace AwayTwoThree

/-- The canonical `ℤ`-module structure induced by the product algebra. -/
instance algebraModule : Module ℤ AwayTwoThree := Algebra.toModule

/-- The quotient of `AwayTwoThree` by the image of its structure map from `ℤ`. -/
abbrev Cokernel := AwayTwoThree ⧸ LinearMap.range (Algebra.linearMap ℤ AwayTwoThree)

/-- The canonical `ℤ`-module structure on the structure-map cokernel. -/
instance cokernelModule : Module ℤ Cokernel :=
  Submodule.Quotient.module (LinearMap.range (Algebra.linearMap ℤ AwayTwoThree))

/-- The short complex formed by the structure map and its range quotient. -/
def shortComplex : ShortComplex (ModuleCat ℤ) :=
  ModuleCat.shortComplexOfCompEqZero (Algebra.linearMap ℤ AwayTwoThree)
    (LinearMap.range (Algebra.linearMap ℤ AwayTwoThree)).mkQ
    (LinearMap.range_mkQ_comp (Algebra.linearMap ℤ AwayTwoThree))

/-- The structure-map sequence for `AwayTwoThree` is short exact. -/
theorem shortExact : shortComplex.ShortExact := sorry

/-- The structure-map sequence for `AwayTwoThree` does not split over `ℤ`. -/
theorem not_splitting : ¬ Nonempty shortComplex.Splitting := sorry

/-- `AwayTwoThree` is faithfully flat as a `ℤ`-module. -/
instance instFaithfullyFlat : Module.FaithfullyFlat ℤ AwayTwoThree := sorry

/-- The scalar extension of the structure-map short complex to `AwayTwoThree`. -/
def baseChange : ShortComplex (ModuleCat AwayTwoThree) :=
  shortComplex.map (ModuleCat.extendScalars (algebraMap ℤ AwayTwoThree))

/-- A retraction of the base-changed structure map. -/
def retraction :
    AwayTwoThree ⊗[ℤ] AwayTwoThree →ₗ[AwayTwoThree] AwayTwoThree ⊗[ℤ] ℤ :=
  (TensorProduct.AlgebraTensorModule.rid ℤ AwayTwoThree AwayTwoThree).symm.toLinearMap.comp
    (Algebra.TensorProduct.lmul'' ℤ).toLinearMap

/-- The retraction sends a tensor-square element to its product tensored with `1`. -/
theorem retraction_apply (z : AwayTwoThree ⊗[ℤ] AwayTwoThree) :
    retraction z = (Algebra.TensorProduct.lmul'' ℤ).toLinearMap z ⊗ₜ (1 : ℤ) := sorry

/-- The retraction is a left inverse to the base-changed structure map. -/
theorem retraction_comp_baseChange :
    retraction.comp (LinearMap.baseChange AwayTwoThree (Algebra.linearMap ℤ AwayTwoThree)) =
      (LinearMap.id : AwayTwoThree ⊗[ℤ] ℤ →ₗ[AwayTwoThree] AwayTwoThree ⊗[ℤ] ℤ) := sorry

/-- The scalar-extended short complex is short exact. -/
theorem baseChange_shortExact : baseChange.ShortExact := sorry

/-- The scalar-extended short exact sequence admits a splitting. -/
theorem baseChange_splits : Nonempty baseChange.Splitting := sorry

end AwayTwoThree
end Int
