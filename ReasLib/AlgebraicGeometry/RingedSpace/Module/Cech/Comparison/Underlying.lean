/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Underlying
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Underlying
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying additive Cech comparisons

A module-valued Cech comparison has a canonical additive image.  The source and target
identifications in this file are derived from the exact forgetful functor; they are not extra
choices carried by a comparison package.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech.Comparison

variable {X : RingedSpace.{u}}
variable (U : Opens X.carrier) {ι : Type u}
variable (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)

/-- Forgetting section-module structure sends a fixed derived Cech comparison to a natural
transformation between the canonical additive derived Cech and derived-sections functors. -/
@[stacks 01EQ "underlying additive derived Cech comparison"]
noncomputable def underlying
    (comparison : Comparison U (Opens.Cover.overFamily U 𝒰 h𝒰)) :
    ModuleCech.derivedFunctor 𝒰 ⟶
      Module.Derived.Sections.boundedAbTarget X U :=
  (ModuleCech.Underlying.sourceForgetIso U 𝒰 h𝒰).inv ≫
    Functor.whiskerRight comparison
      (Module.Derived.Sections.underlyingDerivedFunctor X U) ≫
    (Module.Derived.Sections.boundedTargetForgetIso X U).hom

/-- The degree-`p` additive comparison induced by one fixed derived module-valued comparison. -/
@[stacks 01EQ "underlying additive Cech cohomology comparison"]
noncomputable def underlyingDegree
    (comparison : Comparison U (Opens.Cover.overFamily U 𝒰 h𝒰)) (p : ℕ) :
    moduleCechCohomologyFunctor 𝒰 p ⟶
      Module.Derived.Sections.boundedAbCohomologyFunctor X U (p : ℤ) :=
  (ModuleCech.Underlying.homologyIso U 𝒰 h𝒰 p).inv ≫
    Functor.whiskerRight
      (Comparison.degree U (Opens.Cover.overFamily U 𝒰 h𝒰) comparison p)
      (Module.Derived.Sections.forgetFunctor X U) ≫
    (Module.Derived.Sections.boundedCohomologyForgetIso X U (p : ℤ)).hom

/-- The underlying additive degree-`p` comparison at one module sheaf. -/
@[stacks 01EQ "underlying additive Cech comparison component", stacks 01FD
  "underlying additive Cech comparison component"]
abbrev underlyingApp
    (comparison : Comparison U (Opens.Cover.overFamily U 𝒰 h𝒰))
    (F : X.Modules) (p : ℕ) :
    moduleCechCohomology 𝒰 F p ⟶
      (Module.Derived.Sections.boundedAbCohomologyFunctor X U (p : ℤ)).obj F :=
  (underlyingDegree U 𝒰 h𝒰 comparison p).app F

/-- Invertibility of a module-valued comparison at a coefficient sheaf descends to every
underlying additive degree map. -/
@[stacks 01EQ "underlying additive Cech comparison invertibility", stacks 01FD
  "underlying additive Cech comparison invertibility"]
theorem IsIsoAt.underlyingApp
    {comparison : Comparison U (Opens.Cover.overFamily U 𝒰 h𝒰)}
    {F : X.Modules} (h : Comparison.IsIsoAt U
      (Opens.Cover.overFamily U 𝒰 h𝒰) comparison F) (p : ℕ) :
    IsIso (underlyingApp U 𝒰 h𝒰 comparison F p) := by
  exact (((ModuleCech.Underlying.homologyIso U 𝒰 h𝒰 p).app F).symm ≪≫
    (Module.Derived.Sections.forgetFunctor X U).mapIso
      (Comparison.IsIsoAt.appIso U (Opens.Cover.overFamily U 𝒰 h𝒰) h p) ≪≫
    (Module.Derived.Sections.boundedCohomologyForgetIso X U (p : ℤ)).app F).isIso_hom

/-- The underlying additive component isomorphism, with the invertibility certificate consumed
explicitly so callers do not need a proof-local `IsIso` instance. -/
@[stacks 01EQ "underlying additive Cech comparison isomorphism"]
noncomputable def IsIsoAt.underlyingAppIso
    {comparison : Comparison U (Opens.Cover.overFamily U 𝒰 h𝒰)}
    {F : X.Modules} (h : Comparison.IsIsoAt U
      (Opens.Cover.overFamily U 𝒰 h𝒰) comparison F) (p : ℕ) :
    moduleCechCohomology 𝒰 F p ≅
      (Module.Derived.Sections.boundedAbCohomologyFunctor X U (p : ℤ)).obj F :=
  ((ModuleCech.Underlying.homologyIso U 𝒰 h𝒰 p).app F).symm ≪≫
    (Module.Derived.Sections.forgetFunctor X U).mapIso
      (Comparison.IsIsoAt.appIso U (Opens.Cover.overFamily U 𝒰 h𝒰) h p) ≪≫
    (Module.Derived.Sections.boundedCohomologyForgetIso X U (p : ℤ)).app F

/-- The underlying additive component viewed as an `IsIsomorphic` proposition. -/
@[stacks 01EQ "underlying additive Cech comparison isomorphic component"]
theorem IsIsoAt.underlyingApp_isIsomorphic
    {comparison : Comparison U (Opens.Cover.overFamily U 𝒰 h𝒰)}
    {F : X.Modules} (h : Comparison.IsIsoAt U
      (Opens.Cover.overFamily U 𝒰 h𝒰) comparison F) (p : ℕ) :
    IsIsomorphic (moduleCechCohomology 𝒰 F p)
      ((Module.Derived.Sections.boundedAbCohomologyFunctor X U (p : ℤ)).obj F) := sorry

/-- Normalization of a module-valued comparison descends to its degree-zero additive map. -/
@[stacks 01EQ "normalized underlying additive Cech comparison invertibility", stacks 01FD
  "normalized underlying additive Cech comparison invertibility"]
theorem IsNormalized.underlyingApp_zero
    {comparison : Comparison U (Opens.Cover.overFamily U 𝒰 h𝒰)}
    (h : Comparison.IsNormalized U
      (Opens.Cover.overFamily U 𝒰 h𝒰) comparison) (F : X.Modules) :
    IsIso (underlyingApp U 𝒰 h𝒰 comparison F 0) := by
  exact (((ModuleCech.Underlying.homologyIso U 𝒰 h𝒰 0).app F).symm ≪≫
    (Module.Derived.Sections.forgetFunctor X U).mapIso
      (Comparison.IsNormalized.zeroIso U (Opens.Cover.overFamily U 𝒰 h𝒰) h F) ≪≫
    (Module.Derived.Sections.boundedCohomologyForgetIso X U 0).app F).isIso_hom

/-- The degree-zero underlying additive isomorphism supplied by a normalized comparison. -/
@[stacks 01EQ "normalized underlying additive Cech comparison isomorphism"]
noncomputable def IsNormalized.underlyingZeroIso
    {comparison : Comparison U (Opens.Cover.overFamily U 𝒰 h𝒰)}
    (h : Comparison.IsNormalized U
      (Opens.Cover.overFamily U 𝒰 h𝒰) comparison) (F : X.Modules) :
    moduleCechCohomology 𝒰 F 0 ≅
      (Module.Derived.Sections.boundedAbCohomologyFunctor X U 0).obj F :=
  ((ModuleCech.Underlying.homologyIso U 𝒰 h𝒰 0).app F).symm ≪≫
    (Module.Derived.Sections.forgetFunctor X U).mapIso
      (Comparison.IsNormalized.zeroIso U (Opens.Cover.overFamily U 𝒰 h𝒰) h F) ≪≫
    (Module.Derived.Sections.boundedCohomologyForgetIso X U 0).app F

/-- The normalized degree-zero underlying additive component viewed as an `IsIsomorphic`
proposition. -/
@[stacks 01EQ "normalized underlying additive Cech comparison"]
theorem IsNormalized.underlying_zero_isIsomorphic
    {comparison : Comparison U (Opens.Cover.overFamily U 𝒰 h𝒰)}
    (h : Comparison.IsNormalized U
      (Opens.Cover.overFamily U 𝒰 h𝒰) comparison) (F : X.Modules) :
    IsIsomorphic (moduleCechCohomology 𝒰 F 0)
      ((Module.Derived.Sections.boundedAbCohomologyFunctor X U 0).obj F) := sorry

end AlgebraicGeometry.RingedSpace.ModuleCech.Comparison
