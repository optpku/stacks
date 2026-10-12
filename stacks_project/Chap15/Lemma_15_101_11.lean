/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.BaseChange

@[expose] public section

/-!
# Lemma 15.101.11: Ext under ideal-power base change

@stack 0EH0
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open IadicFiniteModuleSystem.Ext.BaseChange

/-
Lemma 15.101.11 (0EH0): let A ⟶ B be a flat homomorphism of Noetherian rings, let I ⊆ A be an
ideal, and let M, N be finite B-modules with M flat over A.  For every nonnegative degree i, the
inverse limit of the quotients `Ext M N i / I ^ (n + 1) • Ext M N i` is canonically isomorphic to
the inverse limit of a strict compatible varying-ring system over `B ⧸ (I B) ^ (n + 1)`, whose
stagewise evaluations recover the reduced Ext stages.  The source's `A`-module wording is not
well-typed for `Ext_B`; this recall uses its `B`-module reading and records the finite-term
hypothesis required by the cited `0EGU` argument.  The reusable owner is the BaseChange leaf;
this file only recalls its source-facing API.
-/

/- Canonical ideal-power system and its base-ring cone. -/
@[stacks 0EH0 "compatibility of base maps with ideal-power transitions"]
#check @quotientBaseMap_compatibility
@[stacks 0EH0 "base-ring cone over the ideal-power tower"]
#check @quotientCone
@[stacks 0EH0 "factorization of the base map to an ideal-power quotient"]
#check @quotientBaseMap_factor
@[stacks 0EH0 "ideal-power extension at a base-change stage"]
#check @ResolutionModel.stageIdeal_eq_map_pow

/- Ambient and reduced Ext stages. -/
@[stacks 0EH0 "ambient Ext quotient tower under flat base change"]
#check @quotientExtTower
@[stacks 0EH0 "module reduction at an ideal-power base-change stage"]
#check @reductionModule
@[stacks 0EH0 "reduced Ext stage over an ideal-power quotient ring"]
#check @reductionExtStage

/- The reusable Hom-window model attached to a finite free resolution. -/
@[stacks 0EH0 "three-term window in a finite-free-resolution Hom complex"]
#check @ResolutionModel.homWindow
@[stacks 0EH0 "Ext as homology of a finite-free-resolution Hom window"]
#check @ResolutionModel.extHomologyIso
@[stacks 0EH0 "strict quotient-Hom tower from a finite free resolution"]
#check @ResolutionModel.tower
@[stacks 0EH0 "canonical tower comparison for Ext under ideal-power base change"]
#check @ResolutionModel.towerComparison
@[stacks 0EH0 "canonical inverse-limit map for Ext under ideal-power base change"]
#check @ResolutionModel.limitComparison
@[stacks 0EH0 "canonical inverse-limit comparison is an isomorphism"]
#check @ResolutionModel.limitComparison_isIso
@[stacks 0EH0 "inverse-limit Ext comparison from an explicit finite Hom window"]
#check @ResolutionModel.limitIsoOfFiniteTerms
@[stacks 0EH0 "forward map of the explicit finite-window Ext comparison"]
#check @ResolutionModel.limitIsoOfFiniteTerms_hom
@[stacks 0EH0 "canonical inverse-limit isomorphism for Ext base change"]
#check @ResolutionModel.limitIso
@[stacks 0EH0 "forward map of the finite-target Ext limit isomorphism"]
#check @ResolutionModel.limitIso_hom
@[stacks 0EGU "finite-term canonical limit isomorphism"]
#check @CategoryTheory.ShortComplex.IdealPower.finiteLimitIso
@[stacks 0EGU "forward map of the finite-term limit isomorphism"]
#check @CategoryTheory.ShortComplex.IdealPower.FiniteTerms.limitIso_hom
@[stacks 0EGU "forward map of the finite-module limit isomorphism"]
#check @CategoryTheory.ShortComplex.IdealPower.finiteLimitIso_hom
@[stacks 0EH0 "stagewise reduced projective resolution"]
#check @ResolutionModel.reducedResolution
@[stacks 0EH0 "finite terms of a finite-resolution Hom window"]
#check @ResolutionModel.HomWindow.finiteTerms

/- Concrete comparison data retained after choosing a finite free resolution. -/
@[stacks 0EH0 "resolution-indexed reduced Ext tower comparison"]
#check @ResolutionComparison
@[stacks 0EH0 "stage of a resolution-indexed reduced Ext tower"]
#check @ResolutionComparison.stage
@[stacks 0EH0 "transition of a resolution-indexed reduced Ext tower"]
#check @ResolutionComparison.step
@[stacks 0EH0 "stage identification for a resolution-indexed reduced Ext tower"]
#check @ResolutionComparison.stageIsomorphic
@[stacks 0EH0 "A-restricted tower of a resolution-indexed Ext comparison"]
#check @ResolutionComparison.towerOverA
@[stacks 0EH0 "A-restricted transition of a resolution-indexed Ext comparison"]
#check @ResolutionComparison.stepOverA
@[stacks 0EH0 "tower map of a resolution-indexed reduced Ext comparison"]
#check @ResolutionComparison.towerComparison
@[stacks 0EH0 "limit map of a resolution-indexed reduced Ext comparison"]
#check @ResolutionComparison.limitComparison
@[stacks 0EH0 "limit isomorphism of a resolution-indexed reduced Ext comparison"]
#check @ResolutionComparison.limitIso
@[stacks 0EH0 "forward map of the resolution-indexed limit isomorphism"]
#check @ResolutionComparison.limitIso_hom
@[stacks 0EH0 "comparison data from an explicit finite Hom window"]
#check @ResolutionComparison.ofFiniteTerms
@[stacks 0EH0 "concrete comparison data from a chosen finite free resolution"]
#check @ResolutionComparison.ofResolution

/- Source-facing existential corollary, checked at its complete expected type. -/
section

universe u v

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B] [Small.{v} B]
variable (I : Ideal A) (M N : ModuleCat.{v} B)
variable [Module.Finite B M] [Module.Finite B N]
variable (hBflat : (algebraMap A B).Flat)
variable (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
variable (i : ℕ)

@[stacks 0EH0 "limit comparison for Ext under flat ideal-power base change"]
#check (existsReductionTowerComparison I M N hBflat hMflat i :
  ∃ T : ModuleSystem.{u, v} (quotientRingSystem (A := A) (B := B) I),
    ∃ α : quotientExtTower I M N i ⟶ reductionTowerOverA I T,
      ∃ e : limit (quotientExtTower I M N i) ≅ limit (reductionTowerOverA I T),
        (∀ n : ℕ,
          IsIsomorphic ((reductionEvaluation I n).obj T)
            (reductionExtStage I M N i n)) ∧
          e.hom = Limits.lim.map α)

end

#print axioms IadicFiniteModuleSystem.Ext.BaseChange.ResolutionModel.tower
#print axioms IadicFiniteModuleSystem.Ext.BaseChange.ResolutionModel.towerComparison
#print axioms IadicFiniteModuleSystem.Ext.BaseChange.ResolutionModel.limitComparison
#print axioms IadicFiniteModuleSystem.Ext.BaseChange.ResolutionModel.limitIsoOfFiniteTerms
#print axioms IadicFiniteModuleSystem.Ext.BaseChange.ResolutionModel.reducedResolution
#print axioms IadicFiniteModuleSystem.Ext.BaseChange.ResolutionComparison.ofResolution
