/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.MeromorphicSection.NoEmbeddedPoints
import StacksCheckRecall

universe u

/- Lemma 31.24.3 (1): on a locally Noetherian scheme without embedded points, the
meromorphic-function sheaf is the product of the pushed-forward local-ring sheaves at the
generic points. -/
@[stacks 0EMH]
#check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.NoEmbeddedPoints.sheaf_iso_genericPointStalkPushforwardProduct :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      X.embeddedPoints = (∅ : Set X) →
        CategoryTheory.IsIsomorphic X.toLocallyRingedSpace.meromorphicFunctionSheaf
          (AlgebraicGeometry.genericPointStalkPushforwardProductSheaf X))

/- The direct sum of the pushed-forward generic-point stalks agrees with their product. -/
#check
  (AlgebraicGeometry.genericPointStalkPushforwardCoproduct_isIsomorphic_product :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (ℱ : X.Modules),
      CategoryTheory.IsIsomorphic
        (AlgebraicGeometry.genericPointStalkPushforwardCoproductModule X ℱ)
        (AlgebraicGeometry.genericPointStalkPushforwardProductModule X ℱ))

/- Lemma 31.24.3 (2): on a locally Noetherian scheme without embedded points, the
meromorphic-function algebra is quasicoherent as a module over the structure sheaf. -/
@[stacks 0EMH]
#check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.NoEmbeddedPoints.sheaf_isQuasicoherent :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      X.embeddedPoints = (∅ : Set X) →
        ((SheafOfModules.RingedSite.restrictionAlong
          X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
            (SheafOfModules.unit
              (SheafOfModules.RingedSite.ringSheaf
                (Opens.grothendieckTopology X.toTopCat)
                X.toLocallyRingedSpace.meromorphicFunctionSheaf) :
              SheafOfModules.RingedSite.ringedSiteModuleCategory
                (Opens.grothendieckTopology X.toTopCat)
                X.toLocallyRingedSpace.meromorphicFunctionSheaf)).IsQuasicoherent)

/- The sheaf of meromorphic functions is bundled as a quasicoherent algebra over the structure
sheaf. -/
#check
  (AlgebraicGeometry.Scheme.meromorphicFunctionQcAlgebra :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      X.weakAss ⊆ genericPoints X → X.QcAlgebraUnder)

/- Lemma 31.24.3 (3): the meromorphic-section sheaf of every quasicoherent module is the
product of the pushed-forward stalks at the generic points. -/
@[stacks 0EMH]
#check
  (AlgebraicGeometry.Scheme.Module.MeromorphicSection.NoEmbeddedPoints.sheaf_isIsomorphic_genericPointStalkPushforwardProduct :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]
      (_ : X.embeddedPoints = (∅ : Set X)) (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      CategoryTheory.IsIsomorphic
        ((SheafOfModules.RingedSite.restrictionAlong
          X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
            (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ))
        (AlgebraicGeometry.genericPointStalkPushforwardProductModule X ℱ))

/- Lemma 31.24.3 (4): the meromorphic-section sheaf of every quasicoherent module is
quasicoherent over the structure sheaf. -/
@[stacks 0EMH]
#check
  (AlgebraicGeometry.Scheme.Module.MeromorphicSection.NoEmbeddedPoints.sheaf_isQuasicoherent :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]
      (_ : X.embeddedPoints = (∅ : Set X)) (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      ((SheafOfModules.RingedSite.restrictionAlong
        X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
          (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ)).IsQuasicoherent)

/- Lemma 31.24.3 (5): the rational-function ring is the ring of global meromorphic
functions. -/
@[stacks 0EMH]
#check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.NoEmbeddedPoints.rationalFunctionRing_iso_meromorphicFunctions :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      X.embeddedPoints = (∅ : Set X) →
        CategoryTheory.IsIsomorphic X.rationalFunctionRing
          X.toLocallyRingedSpace.meromorphicFunctions)
