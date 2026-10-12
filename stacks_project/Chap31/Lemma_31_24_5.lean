/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Denominator.Product
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 31.24.5: for a locally Noetherian scheme `X`, an invertible
`𝒪_X`-module `ℒ`, a regular meromorphic section `s`, and a coherent module
sheaf `ℱ` with full support and no embedded associated points, the denominator
product `Iℱ` has canonical injective maps to `ℱ` and `ℱ ⊗ ℒ`; both cokernels
are supported on the denominator support. -/
@[stacks 02P2] #check
  (AlgebraicGeometry.Scheme.denominatorIdealProduct_maps :
    {X : AlgebraicGeometry.Scheme.{u}} →
      [AlgebraicGeometry.IsLocallyNoetherian X] →
      (ℒ : X.Modules) →
      [AlgebraicGeometry.Scheme.Modules.Invertible ℒ] →
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ) →
      X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s →
      (ℱ : X.Modules) →
      [ℱ.IsCoherent] →
      AlgebraicGeometry.Scheme.Modules.embeddedAssociatedPoints ℱ = (∅ : Set X) →
      AlgebraicGeometry.RingedSpace.moduleSupport ℱ = Set.univ →
      (Mono (AlgebraicGeometry.Scheme.denominatorIdealProduct ℒ s ℱ).arrow ∧
        AlgebraicGeometry.RingedSpace.moduleSupport
            (cokernel (AlgebraicGeometry.Scheme.denominatorIdealProduct ℒ s ℱ).arrow) ⊆
          AlgebraicGeometry.Scheme.denominatorSupport ℒ s) ∧
        ∃! σ : Subobject.underlying.obj
            (AlgebraicGeometry.Scheme.denominatorIdealProduct ℒ s ℱ) ⟶ ℱ ⊗ ℒ,
          AlgebraicGeometry.Scheme.denominatorIdealProductFactor ℒ s ℱ ≫ σ =
              AlgebraicGeometry.Scheme.denominatorSectionTensorMap ℒ s ℱ ∧
            Mono σ ∧
            AlgebraicGeometry.RingedSpace.moduleSupport (cokernel σ) ⊆
              AlgebraicGeometry.Scheme.denominatorSupport ℒ s)
