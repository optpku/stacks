module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech.DeltaFunctor
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Derived
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.LeftExact
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Effaceable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Universality of ringed-site Cech cohomology

For a covering family, positive Cech cohomology of an injective presheaf module vanishes. This
makes the positive degree functors effaceable and hence makes the canonical Cech delta functor
universal. The statements remain at the presheaf-module layer required by Cech cohomology; no
sheafification or forgetful comparison is built into this owner.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.CohomologicalDeltaFunctor

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{w}) (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)

/-- Positive successor Cech cohomology vanishes on injective presheaf modules for a covering
family. -/
@[stacks 01EN "injective presheaves are Cech-acyclic"]
theorem isZero_of_injectivePresheaf_succ
    (I : PresheafOfModules.{w} 𝒪.obj) [Injective I] (n : ℕ) :
    IsZero (((degree 𝒪 U family (n + 1)).obj).obj I) := sorry

/-- Positive Cech cohomology vanishes on an injective presheaf module. -/
@[stacks 01EN "positive Cech acyclicity of injective presheaves"]
theorem isZero_of_injectivePresheaf_pos
    (I : PresheafOfModules.{w} 𝒪.obj) [Injective I] (n : ℕ) (hn : 0 < n) :
    IsZero (((degree 𝒪 U family n).obj).obj I) := sorry

/-- Every positive degree of Cech cohomology for a covering family is effaceable. -/
@[stacks 01EN "effaceability of positive Cech cohomology"]
theorem degree_isEffaceable
    [EnoughInjectives (PresheafOfModules.{w} 𝒪.obj)]
    (n : ℕ) (hn : 0 < n) :
    ((degree 𝒪 U family n).obj).IsEffaceable := sorry

/-- The Cech cohomology delta functor on presheaf modules is universal. -/
@[stacks 01EN "universality of the ringed-site module Cech delta functor"]
instance deltaFunctor.isUniversal
    [EnoughInjectives (PresheafOfModules.{w} 𝒪.obj)]
    :
    IsUniversal (deltaFunctor 𝒪 U family) := sorry

/-- Lemma 20.10.5 (Tag 01EN): a covering family has the universal Cech cohomology
delta functor supplied by the canonical presheaf-module owner. -/
@[stacks 01EN "covering-family source bridge for Cech universality"]
theorem deltaFunctor_isUniversal_of_coversTop
    [EnoughInjectives (PresheafOfModules.{w} 𝒪.obj)]
    (hfamily : (J.over U).CoversTop family) :
    IsUniversal (deltaFunctor 𝒪 U family) := sorry

end SheafOfModules.RingedSite.Cech
