module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.PrincipalPower.Tower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Delta
public import stacks_project.Chap20.Lemma_20_36_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.CohomologicalDeltaFunctor
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Delta
open scoped PrincipalPower

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-!
The four clauses of Remark 20.36.6 are a geometric specialization of
`CohomologicalDeltaFunctor.PrincipalPower`.  The shared owner uses categorical kernels and
cokernels; the chapter aliases below expose the same indexing (`n` represents the source's
positive exponent `n + 1`) without introducing a second quotient or torsion representation.
-/

section

variable (f : globalSectionsRing X) (ℱ : X.Modules) (p : ℕ)

/-- The tower `n ↦ H^p(X, ℱ / f^(n + 1)ℱ)` in the categorical cokernel model. -/
@[stacks 0H3A "principal-power quotient cohomology tower"]
abbrev globalSectionPowerQuotientCohomologyTower :
    SequentialInverseSystem (ModuleCat (globalSectionsRing X)) :=
  CategoryTheory.CohomologicalDeltaFunctor.PrincipalPower.quotientSystem
    (cohomology X) f ℱ p

/-- The degree-`p` tower `n ↦ H^p(X, ℱ)[f^(n + 1)]` in the categorical kernel model. -/
@[stacks 0H3A "principal-power torsion cohomology tower"]
abbrev globalCohomologyPowerTorsionTower :
    SequentialInverseSystem (ModuleCat (globalSectionsRing X)) :=
  CategoryTheory.Linear.PrincipalPower.kernelSystem f
    (((cohomology X).F p).obj.obj ℱ)

/-- The quotient comparison map from the cohomology of `ℱ` to the quotient cohomology tower. -/
@[stacks 0H3A "principal-power quotient comparison"]
noncomputable abbrev cohomologyTowerQuotientMap :
    CategoryTheory.Linear.PrincipalPower.quotientSystem f
        (((cohomology X).F p).obj.obj ℱ) ⟶
      globalSectionPowerQuotientCohomologyTower f ℱ p :=
  CategoryTheory.CohomologicalDeltaFunctor.PrincipalPower.quotientMap
    (cohomology X) f ℱ p

/-- The scalar-action formula used by the source-facing description of the quotient map. -/
@[stacks 0H3A "global cohomology preserves principal-power scalar actions"]
theorem globalCohomologyDegree_map_globalSectionMulPow_eq_smul (n : ℕ) :
    ((cohomology X).F p).obj.map
        (globalSectionMul (f ^ n) ℱ) =
      (f ^ n) • 𝟙 (((cohomology X).F p).obj.obj ℱ) := sorry

/-- The boundary map from quotient cohomology to the next-degree power-kernel tower.

The explicit source hypothesis is converted once to the canonical categorical `Mono` instance.
This is a compatibility boundary only; all subsequent constructions consume the generic owner. -/
@[stacks 0H3A "principal-power cohomology boundary"]
noncomputable def cohomologyTowerBoundaryMap
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    globalSectionPowerQuotientCohomologyTower f ℱ p ⟶
      globalCohomologyPowerTorsionTower f ℱ (p + 1) :=
  letI : CategoryTheory.Linear.PrincipalPower.IsTorsionFree f ℱ :=
    -- Local instance justification (proof-local temporary data): the source hypothesis is an
    -- explicit certificate and is converted only for this generic boundary construction.
    GlobalSections.Power.isTorsionFree_of f ℱ hℱ
  CategoryTheory.CohomologicalDeltaFunctor.PrincipalPower.boundaryMap
    (cohomology X) f ℱ p

/-- The canonical short complex of quotient, cohomology, and torsion towers. -/
@[stacks 0H3A "principal-power cohomology short complex"]
noncomputable def cohomologyTowerShortComplex
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    ShortComplex
      (SequentialInverseSystem (ModuleCat (globalSectionsRing X))) :=
  -- Local instance justification (proof-local temporary data): this pins the same explicit source
  -- certificate while selecting the shared short-complex owner; it is not a global fact.
  letI : CategoryTheory.Linear.PrincipalPower.IsTorsionFree f ℱ :=
    GlobalSections.Power.isTorsionFree_of f ℱ hℱ
  CategoryTheory.CohomologicalDeltaFunctor.PrincipalPower.shortComplex
    (cohomology X) f ℱ p

/-- The inverse-limit short complex attached to the principal-power tower. -/
@[stacks 0H3A "principal-power cohomology completion"]
noncomputable abbrev cohomologyCompletionShortComplex
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    ShortComplex (ModuleCat (globalSectionsRing X)) :=
  -- Local instance justification (proof-local temporary data): the completion owner has a
  -- typeclass input, but the chapter exposes the source assumption explicitly.
  letI : CategoryTheory.Linear.PrincipalPower.IsTorsionFree f ℱ :=
    GlobalSections.Power.isTorsionFree_of f ℱ hℱ
  CategoryTheory.CohomologicalDeltaFunctor.PrincipalPower.completionShortComplex
    (cohomology X) f ℱ p

namespace CohomologyTower

/-- The left term is the principal-power quotient tower of `H^p(X, ℱ)`. -/
@[simp, stacks 0H3A "left tower in the principal-power cohomology sequence"]
theorem left (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyTowerShortComplex f ℱ p hℱ).X₁ =
      CategoryTheory.Linear.PrincipalPower.quotientSystem f
        (((cohomology X).F p).obj.obj ℱ) := sorry

/-- The middle term is the tower `n ↦ H^p(X, ℱ / f^(n+1)ℱ)`. -/
@[simp, stacks 0H3A "middle tower in the principal-power cohomology sequence"]
theorem middle (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyTowerShortComplex f ℱ p hℱ).X₂ =
      globalSectionPowerQuotientCohomologyTower f ℱ p := sorry

/-- The right term is the tower `n ↦ H^(p+1)(X, ℱ)[f^(n+1)]`. -/
@[simp, stacks 0H3A "right tower in the principal-power cohomology sequence"]
theorem right (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyTowerShortComplex f ℱ p hℱ).X₃ =
      globalCohomologyPowerTorsionTower f ℱ (p + 1) := sorry

end CohomologyTower

namespace CohomologyCompletion

/-- The left completion term is the limit of the principal-power quotient tower of
`H^p(X, ℱ)`. -/
@[simp, stacks 0H3A "left term in the principal-power cohomology completion"]
theorem left (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyCompletionShortComplex f ℱ p hℱ).X₁ =
      limit (CategoryTheory.Linear.PrincipalPower.quotientSystem f
        (((cohomology X).F p).obj.obj ℱ)) := sorry

/-- The middle completion term is `lim_n H^p(X, ℱ / f^(n+1)ℱ)`. -/
@[simp, stacks 0H3A "middle term in the principal-power cohomology completion"]
theorem middle (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyCompletionShortComplex f ℱ p hℱ).X₂ =
      limit (globalSectionPowerQuotientCohomologyTower f ℱ p) := sorry

/-- The right completion term is the principal Tate module of `H^(p+1)(X, ℱ)`. -/
@[simp, stacks 0H3A "right term in the principal-power cohomology completion"]
theorem right (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyCompletionShortComplex f ℱ p hℱ).X₃ =
      T[f] (((cohomology X).F (p + 1)).obj.obj ℱ) := sorry

end CohomologyCompletion

/- The source proposition is retained as an ordinary theorem rather than an instance: it carries an
explicit module and section, so registering it globally would pollute typeclass search. -/

/-- Remark 20.36.6 (1): the principal-power cohomology tower is short exact. -/
@[stacks 0H3A]
theorem cohomologyTowerShortComplex_shortExact
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyTowerShortComplex f ℱ p hℱ).ShortExact := sorry

/-- Remark 20.36.6 (2): taking the inverse limit preserves the short exact tower sequence. -/
@[stacks 0H3A]
theorem cohomologyCompletionShortComplex_shortExact
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (cohomologyCompletionShortComplex f ℱ p hℱ).ShortExact := sorry

/-- The concrete `R¹ lim` comparison isomorphism for the source-facing towers. -/
@[stacks 0H3A "principal-power cohomology first derived limit iso"]
noncomputable def cohomologyTower_firstDerivedLimitIso
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    (globalSectionPowerQuotientCohomologyTower f ℱ p).firstDerivedLimit ≅
      (globalCohomologyPowerTorsionTower f ℱ (p + 1)).firstDerivedLimit :=
  -- Local instance justification (proof-local temporary data): only the generic iso constructor
  -- needs the converted `Mono` certificate; registering it globally would over-constrain search.
  letI : CategoryTheory.Linear.PrincipalPower.IsTorsionFree f ℱ :=
    GlobalSections.Power.isTorsionFree_of f ℱ hℱ
  CategoryTheory.CohomologicalDeltaFunctor.PrincipalPower.firstDerivedLimitIso
    (cohomology X) f ℱ p

/-- Remark 20.36.6 (3): the induced map on first derived inverse limits is an isomorphism. -/
@[stacks 0H3A]
theorem cohomologyTower_firstDerivedLimitMap_isIso
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    IsIso (SequentialInverseSystem.firstDerivedLimitMap
      (cohomologyTowerBoundaryMap f ℱ p hℱ)) :=
  (cohomologyTower_firstDerivedLimitIso f ℱ p hℱ).isIso_hom

/-- Remark 20.36.6 (4): the quotient cohomology tower is Mittag-Leffler exactly when the torsion
tower is Mittag-Leffler. -/
@[stacks 0H3A]
theorem cohomologyTower_isMittagLeffler_iff_torsion
    (hℱ : IsTorsionFreeByGlobalSection f ℱ) :
    IsMittagLeffler (globalSectionPowerQuotientCohomologyTower f ℱ p) ↔
      IsMittagLeffler (globalCohomologyPowerTorsionTower f ℱ (p + 1)) := sorry

end

/- The label-facing checks are direct references to the shared declarations, not wrapper theorems. -/
@[stacks 0H3A]
#check @CategoryTheory.CohomologicalDeltaFunctor.PrincipalPower.shortComplex_shortExact

@[stacks 0H3A]
#check @CategoryTheory.CohomologicalDeltaFunctor.PrincipalPower.completionShortComplex_shortExact

@[stacks 0H3A]
#check @CategoryTheory.CohomologicalDeltaFunctor.PrincipalPower.firstDerivedLimitMap_isIso

@[stacks 0H3A]
#check @CategoryTheory.CohomologicalDeltaFunctor.PrincipalPower.isMittagLeffler_iff_torsion

#check @cohomologyTowerShortComplex
#check @cohomologyCompletionShortComplex
#check @cohomologyTower_firstDerivedLimitIso
#check @CohomologyTower.left
#check @CohomologyTower.middle
#check @CohomologyTower.right
#check @CohomologyCompletion.left
#check @CohomologyCompletion.middle
#check @CohomologyCompletion.right

end AlgebraicGeometry.RingedSpace
