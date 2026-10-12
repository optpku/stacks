/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction.FiniteComponents
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Meromorphic sections on schemes with locally finite components

Meromorphic sections of a quasi-coherent module can be described as a locally finite sum, or
equivalently a product, of direct images of the module stalks at generic points.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The direct image on `X` of the affine module sheaf associated to the stalk of a module at a
generic point. -/
noncomputable abbrev genericPointStalkPushforwardModule
    (ℱ : X.Modules) (η : genericPoints X) : X.Modules :=
  (Scheme.Modules.pushforward (genericPointStalkMap X η)).obj
    (tilde (RingedSpace.stalkModuleCat ℱ η.1))

/-- The coproduct of the direct images of a module's generic-point stalks. -/
noncomputable abbrev genericPointStalkPushforwardCoproductModule
    (ℱ : X.Modules) : X.Modules :=
  ∐ fun η : genericPoints X ↦ genericPointStalkPushforwardModule X ℱ η

/-- The product of the direct images of a module's generic-point stalks. -/
noncomputable abbrev genericPointStalkPushforwardProductModule
    (ℱ : X.Modules) : X.Modules :=
  ∏ᶜ fun η : genericPoints X ↦ genericPointStalkPushforwardModule X ℱ η

/-- For a scheme with finitely many components on quasi-compact opens, the coproduct and product
of the direct images of any module's generic-point stalks are isomorphic. -/
theorem genericPointStalkPushforwardCoproduct_isIsomorphic_product
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] (ℱ : X.Modules) :
    IsIsomorphic (genericPointStalkPushforwardCoproductModule X ℱ)
      (genericPointStalkPushforwardProductModule X ℱ) := sorry

/-- Under finite-component and weak-association hypotheses, the underlying structure-sheaf
module of the meromorphic sections of a quasi-coherent module is isomorphic to the product of
the direct images of its generic-point stalks. -/
theorem meromorphicSectionSheaf_isIsomorphic_genericPointStalkPushforwardProduct
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ genericPoints X)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
        (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ))
      (genericPointStalkPushforwardProductModule X ℱ) := sorry

/-- Under finite-component and weak-association hypotheses, the underlying structure-sheaf
module of the meromorphic sections of a quasi-coherent module is quasi-coherent. -/
theorem meromorphicSectionSheaf_isQuasicoherent
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ genericPoints X)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
      (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ)).IsQuasicoherent := sorry

end AlgebraicGeometry
