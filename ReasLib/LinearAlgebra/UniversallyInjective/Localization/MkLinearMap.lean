/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective
public import ReasLib.RingTheory.Localization.TensorProduct

/-!
# Universal injectivity of localization maps

This file relates universal injectivity of the action of every denominator to universal
injectivity of the canonical map into a localized module.
-/

@[expose] public section

universe u v w z

namespace LocalizedModule

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]

/-- If every denominator acts universally injectively on a module, then the canonical map to
the localized module is universally injective after restricting scalars. -/
theorem universallyInjective_mkLinearMap (T : Submonoid A)
    (hT : ∀ s : T, LinearMap.UniversallyInjective.{u, w, w, z}
      (DistribSMul.toLinearMap R M (s : A))) :
    LinearMap.UniversallyInjective.{u, w, max v w, z}
      ((mkLinearMap T M).restrictScalars R) := sorry

end LocalizedModule
