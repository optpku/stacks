module

import ReasLib.AlgebraicGeometry.Scheme.Module.MeromorphicSection.FiniteComponents
import StacksCheckRecall

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

/- Lemma 31.23.6 (1): the meromorphic-function sheaf is the product of the direct images of the
local rings at the generic points of the irreducible components. -/
@[stacks 0EMF] #check
  (AlgebraicGeometry.meromorphicFunctionSheaf_iso_genericPointStalkPushforwardProduct :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      X.weakAss ⊆ genericPoints X →
        IsIsomorphic X.toLocallyRingedSpace.meromorphicFunctionSheaf
          (AlgebraicGeometry.genericPointStalkPushforwardProductSheaf X))

/- Lemma 31.23.6 (2): the coproduct and product of the pushed-forward generic-point stalk
modules agree. -/
@[stacks 0EMF] #check
  (AlgebraicGeometry.genericPointStalkPushforwardCoproduct_isIsomorphic_product :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (ℱ : X.Modules),
      IsIsomorphic
        (AlgebraicGeometry.genericPointStalkPushforwardCoproductModule X ℱ)
        (AlgebraicGeometry.genericPointStalkPushforwardProductModule X ℱ))

/- Lemma 31.23.6 (3): the meromorphic-function algebra is quasi-coherent as a module over the
structure sheaf. -/
@[stacks 0EMF] #check
  (AlgebraicGeometry.meromorphicFunctionSheaf_isQuasicoherent :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      X.weakAss ⊆ genericPoints X →
        ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
          (SheafOfModules.unit
            (ringSheaf (Opens.grothendieckTopology X.toTopCat)
              X.toLocallyRingedSpace.meromorphicFunctionSheaf) :
            ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat)
              X.toLocallyRingedSpace.meromorphicFunctionSheaf)).IsQuasicoherent)

/- Lemma 31.23.6 (4): the meromorphic-function sheaf is bundled as a quasi-coherent algebra over
the structure sheaf. -/
@[stacks 0EMF] #check
  (AlgebraicGeometry.Scheme.meromorphicFunctionQcAlgebra :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      X.weakAss ⊆ genericPoints X → X.QcAlgebraUnder)

/- Lemma 31.23.6 (5): the meromorphic-section module is the product of the direct images of its
generic-point stalks. -/
@[stacks 0EMF] #check
  (AlgebraicGeometry.meromorphicSectionSheaf_isIsomorphic_genericPointStalkPushforwardProduct :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (hweak : X.weakAss ⊆ genericPoints X)
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      IsIsomorphic
        ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
          (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ))
        (AlgebraicGeometry.genericPointStalkPushforwardProductModule X ℱ))

/- Lemma 31.23.6 (6): the meromorphic-section module of a quasi-coherent module is
quasi-coherent. -/
@[stacks 0EMF] #check
  (AlgebraicGeometry.meromorphicSectionSheaf_isQuasicoherent :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (hweak : X.weakAss ⊆ genericPoints X)
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
        (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ)).IsQuasicoherent)

/- Lemma 31.23.6 (7): the stalk of canonical meromorphic denominators is the submonoid of
non-zero-divisors in the local ring. -/
@[stacks 0EMF] #check
  (AlgebraicGeometry.meromorphicDenominatorStalk_eq_nonZeroDivisors :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      X.weakAss ⊆ genericPoints X → ∀ x : X,
        AlgebraicGeometry.meromorphicDenominatorStalk X x =
          nonZeroDivisors (X.presheaf.stalk x))

/- Lemma 31.23.6 (8): every meromorphic-function stalk is the total quotient ring of the local
ring. -/
@[stacks 0EMF] #check
  (AlgebraicGeometry.meromorphicStalk_isLocalization :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      X.weakAss ⊆ genericPoints X → ∀ x : X,
        IsLocalization (nonZeroDivisors (X.presheaf.stalk x))
          (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk x))

/- Lemma 31.23.6 (9): meromorphic functions on an affine open form the total quotient ring of
its regular functions. -/
@[stacks 0EMF] #check
  (AlgebraicGeometry.meromorphicSections_isLocalization_of_isAffineOpen :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      X.weakAss ⊆ genericPoints X → ∀ (U : X.Opens), AlgebraicGeometry.IsAffineOpen U →
        IsLocalization (nonZeroDivisors Γ(X, U))
          (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.obj (op U)))

/- Lemma 31.23.6 (10): the rational-function ring is the ring of global meromorphic
functions. -/
@[stacks 0EMF] #check
  (AlgebraicGeometry.rationalFunctionRing_iso_meromorphicFunctions :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      X.weakAss ⊆ genericPoints X →
        IsIsomorphic X.rationalFunctionRing X.toLocallyRingedSpace.meromorphicFunctions)
