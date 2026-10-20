/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Sections

/-!
# Regular meromorphic sections on algebraic spaces

A meromorphic section of an `𝒪_X`-module is regular when the induced morphism
`𝒦_X ⟶ 𝒦_X(F)` is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The morphism `𝒦_X ⟶ 𝒦_X(F)` induced by a meromorphic section of `F`. -/
abbrev meromorphicSectionMap (F : X.Modules) (s : meromorphicSections X F) :
    unitModule (smallEtaleTopology X) (meromorphicFunctionSheaf X) ⟶
      meromorphicSectionSheaf X F :=
  (meromorphicSectionSheaf X F).unitHomEquiv.symm s

/-- A meromorphic section is regular when its induced map `𝒦_X ⟶ 𝒦_X(F)` is a
monomorphism. -/
abbrev IsRegularMeromorphicSection (F : X.Modules) (s : meromorphicSections X F) : Prop :=
  Mono (meromorphicSectionMap X F s)

/-- A meromorphic section is regular exactly when its induced morphism is a monomorphism. -/
theorem isRegularMeromorphicSection_iff_mono (F : X.Modules) (s : meromorphicSections X F) :
    IsRegularMeromorphicSection X F s ↔ Mono (meromorphicSectionMap X F s) :=
  sorry

/-- Regularity of a meromorphic section is objectwise injectivity of the induced map
`𝒦_X ⟶ 𝒦_X(F)`. -/
theorem isRegularMeromorphicSection_iff_injective (F : X.Modules)
    (s : meromorphicSections X F) :
    IsRegularMeromorphicSection X F s ↔
      ∀ U : (smallEtaleSite X)ᵒᵖ,
        Function.Injective ((meromorphicSectionMap X F s).val.app U).hom :=
  sorry

/-- The morphism induced by a meromorphic section recovers that section under `unitHomEquiv`. -/
theorem unitHomEquiv_meromorphicSectionMap (F : X.Modules) (s : meromorphicSections X F) :
    (meromorphicSectionSheaf X F).unitHomEquiv (meromorphicSectionMap X F s) = s :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
