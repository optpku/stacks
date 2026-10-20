module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.ComplexTower
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import ReasLib.CategoryTheory.Sites.EnoughObjects
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology comparison for complex towers

This leaf owns the two canonical maps attached to a sequential inverse system of complexes of
modules on a ringed site:

* `comparison` is the cohomology-sheaf map produced by `limit.post`;
* `projection` is the stage projection from the inverse limit of cohomology sheaves.

The basiswise hypotheses are kept as separate, atomic statements.  The chapter-facing names in
`RingedSite.Hom` are compatibility bridges; downstream developments should prefer the shorter
names in `RingedSite.Hom.ModuleSections.Limit`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open RingedSite.Hom.ModuleSections.Underlying

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleSections.Limit

variable (X : RingedSite.{u, v, w})
variable [CategoryWithHomology (RingedSite.ModuleCat.{z} X)]

/-- The cohomology-sheaf comparison map `H^m(lim F) ⟶ lim H^m(F)`. -/
@[stacks 08CT "cohomology-sheaf comparison map"]
abbrev comparison
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (m : ℤ)
    [HasLimit F]
    [HasLimit (cohomologySheafTower.{z} X F m)] :=
  limit.post F (cohomologySheaf.{z} X m)

/-- The projection from the inverse limit of cohomology sheaves to stage `n₀`. -/
@[stacks 08CT "cohomology-sheaf stage projection"]
abbrev projection
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (m : ℤ) (n₀ : ℕ)
    [HasLimit (cohomologySheafTower.{z} X F m)] :=
  limit.π (cohomologySheafTower.{z} X F m) (op n₀)

/-- Basiswise `R¹ lim` vanishing gives bijectivity of `comparison` on a basis object. -/
@[stacks 08CT "basiswise cohomology comparison bijectivity"]
theorem comparison_app_bijective_of_basiswise_r1
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (m : ℤ) (B : Set X)
    [HasLimit F]
    [HasLimit (cohomologySheafTower.{z} X F m)]
    (hdegree₂ : ∀ U : X, U ∈ B →
      IsZero ((complexDegreeTower.{z} X F U (m - 2)).firstDerivedLimit))
    (hdegree₁ : ∀ U : X, U ∈ B →
      IsZero ((complexDegreeTower.{z} X F U (m - 1)).firstDerivedLimit))
    (hcohom₁ : ∀ U : X, U ∈ B →
      IsZero ((complexCohomologyTower.{z} X F U (m - 1)).firstDerivedLimit))
    (U : X) (hU : U ∈ B) :
    Function.Bijective ((comparison X F m).1.app (op U)) := sorry

/-- A basis cover upgrades basiswise bijectivity of `comparison` to an isomorphism. -/
@[stacks 08CT "basiswise cohomology comparison isomorphism"]
theorem comparison_isIso_of_basiswise_r1
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (m : ℤ) (B : Set X)
    [HasLimit F]
    [HasLimit (cohomologySheafTower.{z} X F m)]
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hdegree₂ : ∀ U : X, U ∈ B →
      IsZero ((complexDegreeTower.{z} X F U (m - 2)).firstDerivedLimit))
    (hdegree₁ : ∀ U : X, U ∈ B →
      IsZero ((complexDegreeTower.{z} X F U (m - 1)).firstDerivedLimit))
    (hcohom₁ : ∀ U : X, U ∈ B →
      IsZero ((complexCohomologyTower.{z} X F U (m - 1)).firstDerivedLimit)) :
    IsIso (comparison X F m) := sorry

/-- Transition-map isomorphisms imply eventual constancy of the objectwise cohomology tower. -/
@[stacks 08CT "cohomology tower eventual constancy"]
theorem cohomologyTower_isEventuallyConstantTo_of_transitionMap_isIso
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (i : ℤ) (U : X) (n₀ : ℕ)
    (hconstant : ∀ n : ℕ, ∀ h : n₀ ≤ n,
      IsIso ((complexCohomologyTower.{z} X F U i).transitionMap h)) :
    (complexCohomologyTower.{z} X F U i).IsEventuallyConstantTo (op n₀) := sorry

/-- Eventual constancy recovers the isomorphism of every transition map to the chosen stage. -/
@[stacks 08CT "eventual cohomology tower transition isomorphism"]
theorem cohomologyTower_transitionMap_isIso_of_isEventuallyConstantTo
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (i : ℤ) (U : X) (n₀ n : ℕ) (h : n₀ ≤ n)
    (hconstant :
      (complexCohomologyTower.{z} X F U i).IsEventuallyConstantTo (op n₀)) :
    IsIso ((complexCohomologyTower.{z} X F U i).transitionMap h) := sorry

/-- Basiswise eventual constancy gives bijectivity of the stage projection on a basis object. -/
@[stacks 08CT "basiswise stage projection bijectivity"]
theorem projection_app_bijective_of_basiswise_eventuallyConstant
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (m : ℤ) (B : Set X) (n₀ : ℕ)
    [HasLimit (cohomologySheafTower.{z} X F m)]
    (hconstant : ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ h : n₀ ≤ n,
      IsIso ((complexCohomologyTower.{z} X F U m).transitionMap h))
    (U : X) (hU : U ∈ B) :
    Function.Bijective ((projection X F m n₀).1.app (op U)) := sorry

/-- A basis cover upgrades basiswise eventual constancy to an isomorphism of stage projections. -/
@[stacks 08CT "basiswise stage projection isomorphism"]
theorem projection_isIso_of_basiswise_eventuallyConstant
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (m : ℤ) (B : Set X) (n₀ : ℕ)
    [HasLimit (cohomologySheafTower.{z} X F m)]
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hconstant : ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ h : n₀ ≤ n,
      IsIso ((complexCohomologyTower.{z} X F U m).transitionMap h)) :
    IsIso (projection X F m n₀) := sorry

/-- Canonical formulation of the stage-projection conclusion using `IsEventuallyConstantTo`. -/
@[stacks 08CT "canonical basiswise stage projection isomorphism"]
theorem projection_isIso_of_basiswise_eventuallyConstantTo
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (m : ℤ) (B : Set X) (n₀ : ℕ)
    [HasLimit (cohomologySheafTower.{z} X F m)]
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hconstant : ∀ U : X, U ∈ B →
      (complexCohomologyTower.{z} X F U m).IsEventuallyConstantTo (op n₀)) :
    IsIso (projection X F m n₀) := sorry

/-- The two cohomology-sheaf maps are isomorphisms under their respective basiswise hypotheses. -/
@[stacks 08CT "combined cohomology comparison and projection"]
theorem comparison_and_projection_isIso
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (m : ℤ) (B : Set X) (n₀ : ℕ)
    [HasLimit F]
    [HasLimit (cohomologySheafTower.{z} X F m)]
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hdegree₂ : ∀ U : X, U ∈ B →
      IsZero ((complexDegreeTower.{z} X F U (m - 2)).firstDerivedLimit))
    (hdegree₁ : ∀ U : X, U ∈ B →
      IsZero ((complexDegreeTower.{z} X F U (m - 1)).firstDerivedLimit))
    (hcohom₁ : ∀ U : X, U ∈ B →
      IsZero ((complexCohomologyTower.{z} X F U (m - 1)).firstDerivedLimit))
    (hconstant : ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ h : n₀ ≤ n,
      IsIso ((complexCohomologyTower.{z} X F U m).transitionMap h)) :
    IsIso (comparison X F m) ∧ IsIso (projection X F m n₀) := sorry

end RingedSite.Hom.ModuleSections.Limit

/- Compatibility names for the chapter-facing API.  These declarations deliberately retain the
  old spelling while delegating ownership to the shorter `ModuleSections.Limit` namespace. -/
namespace RingedSite.Hom

variable {X : RingedSite.{u, v}}
variable [CategoryWithHomology (RingedSite.ModuleCat.{max u v} X)]

/-- Compatibility name for `ModuleSections.Limit.comparison_app_bijective_of_basiswise_r1`. -/
@[stacks 08CT]
theorem cohomologySheafLimitComparison_app_bijective_of_basiswise_vanishing_r1lim
    (F : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (m : ℤ) (B : Set X)
    [HasLimit F]
    [HasLimit (underlyingAbelianCohomologySheafInverseSystem X F m)]
    (hdegree_m_sub_two : ∀ U : X, U ∈ B →
      IsZero ((complexSectionDegreeInverseSystem X F U (m - 2)).firstDerivedLimit))
    (hdegree_m_sub_one : ∀ U : X, U ∈ B →
      IsZero ((complexSectionDegreeInverseSystem X F U (m - 1)).firstDerivedLimit))
    (hcohom_m_sub_one : ∀ U : X, U ∈ B →
      IsZero ((complexSectionCohomologyInverseSystem X F U (m - 1)).firstDerivedLimit))
    (U : X) (hU : U ∈ B) :
    Function.Bijective
      ((limit.post F (underlyingAbelianCohomologySheafFunctor X m)).1.app (op U)) := sorry

/-- Compatibility name for `ModuleSections.Limit.comparison_isIso_of_basiswise_r1`. -/
@[stacks 08CT]
theorem cohomologySheafLimitComparison_isIso_of_basiswise_vanishing_r1lim
    (F : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (m : ℤ) (B : Set X)
    [HasLimit F]
    [HasLimit (underlyingAbelianCohomologySheafInverseSystem X F m)]
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hdegree_m_sub_two : ∀ U : X, U ∈ B →
      IsZero ((complexSectionDegreeInverseSystem X F U (m - 2)).firstDerivedLimit))
    (hdegree_m_sub_one : ∀ U : X, U ∈ B →
      IsZero ((complexSectionDegreeInverseSystem X F U (m - 1)).firstDerivedLimit))
    (hcohom_m_sub_one : ∀ U : X, U ∈ B →
      IsZero ((complexSectionCohomologyInverseSystem X F U (m - 1)).firstDerivedLimit)) :
    IsIso (limit.post F (underlyingAbelianCohomologySheafFunctor X m)) := sorry

/-- Compatibility name for the source-to-canonical eventual-constancy bridge. -/
@[stacks 08CT]
theorem complexSectionCohomologyInverseSystem_isEventuallyConstantTo_of_transitionMap_isIso
    (f : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (i : ℤ) (U : X) (n₀ : ℕ)
    (hconstant : ∀ n : ℕ, ∀ h : n₀ ≤ n,
      IsIso ((complexSectionCohomologyInverseSystem X f U i).transitionMap h)) :
    (complexSectionCohomologyInverseSystem X f U i).IsEventuallyConstantTo (op n₀) := sorry

/-- Compatibility name for the canonical-to-source eventual-constancy bridge. -/
@[stacks 08CT]
theorem complexSectionCohomologyInverseSystem_transitionMap_isIso_of_isEventuallyConstantTo
    (f : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (i : ℤ) (U : X) (n₀ n : ℕ) (h : n₀ ≤ n)
    (hconstant :
      (complexSectionCohomologyInverseSystem X f U i).IsEventuallyConstantTo (op n₀)) :
    IsIso ((complexSectionCohomologyInverseSystem X f U i).transitionMap h) := sorry

/-- Compatibility name for basiswise bijectivity of the stage projection. -/
@[stacks 08CT]
theorem cohomologySheafLimitProjection_app_bijective_of_basiswise_eventually_constant
    (f : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (i : ℤ) (B : Set X) (n₀ : ℕ)
    [HasLimit (underlyingAbelianCohomologySheafInverseSystem X f i)]
    (hconstant : ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ h : n₀ ≤ n,
      IsIso ((complexSectionCohomologyInverseSystem X f U i).transitionMap h))
    (U : X) (hU : U ∈ B) :
    Function.Bijective
      ((limit.π (underlyingAbelianCohomologySheafInverseSystem X f i) (op n₀)).1.app
        (op U)) := sorry

/-- Compatibility name for the basiswise stage-projection isomorphism. -/
@[stacks 08CT]
theorem cohomologySheafLimitProjection_isIso_of_basiswise_eventually_constant
    (f : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (i : ℤ) (B : Set X) (n₀ : ℕ)
    [HasLimit (underlyingAbelianCohomologySheafInverseSystem X f i)]
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hconstant : ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ h : n₀ ≤ n,
      IsIso ((complexSectionCohomologyInverseSystem X f U i).transitionMap h)) :
    IsIso (limit.π (underlyingAbelianCohomologySheafInverseSystem X f i) (op n₀)) := sorry

/-- Compatibility name for the canonical eventual-constancy projection theorem. -/
@[stacks 08CT]
theorem cohomologySheafLimitProjection_isIso_of_basiswise_eventuallyConstantTo
    (f : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (i : ℤ) (B : Set X) (n₀ : ℕ)
    [HasLimit (underlyingAbelianCohomologySheafInverseSystem X f i)]
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hconstant : ∀ U : X, U ∈ B →
      (complexSectionCohomologyInverseSystem X f U i).IsEventuallyConstantTo (op n₀)) :
    IsIso (limit.π (underlyingAbelianCohomologySheafInverseSystem X f i) (op n₀)) := sorry

/-- Compatibility name for the combined comparison and projection theorem. -/
@[stacks 08CT]
theorem cohomologySheafLimitComparison_and_projection_isIso_of_basiswise_vanishing_r1lim
    (F : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (m : ℤ) (B : Set X) (n₀ : ℕ)
    [HasLimit F]
    [HasLimit (underlyingAbelianCohomologySheafInverseSystem X F m)]
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hdegree_m_sub_two : ∀ U : X, U ∈ B →
      IsZero ((complexSectionDegreeInverseSystem X F U (m - 2)).firstDerivedLimit))
    (hdegree_m_sub_one : ∀ U : X, U ∈ B →
      IsZero ((complexSectionDegreeInverseSystem X F U (m - 1)).firstDerivedLimit))
    (hcohom_m_sub_one : ∀ U : X, U ∈ B →
      IsZero ((complexSectionCohomologyInverseSystem X F U (m - 1)).firstDerivedLimit))
    (hconstant : ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ h : n₀ ≤ n,
      IsIso ((complexSectionCohomologyInverseSystem X F U m).transitionMap h)) :
    IsIso (limit.post F (underlyingAbelianCohomologySheafFunctor X m)) ∧
      IsIso (limit.π (underlyingAbelianCohomologySheafInverseSystem X F m) (op n₀)) := sorry

end RingedSite.Hom
