module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GrothendieckLarge
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology

/-!
# Cohomology of scheme modules

This leaf specializes the ringed-space module-cohomology interface to schemes,
keeping the open set explicit so that global-section and local cohomology
arguments use the same canonical owner.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Scheme-module categories inherit the canonical injective resolutions of
modules on the underlying ringed space. -/
instance hasInjectiveResolutions (X : Scheme.{u}) :
    HasInjectiveResolutions X.Modules :=
  SheafOfModules.LargeSite.injectiveResolutions
    (Opens.grothendieckTopology X.carrier) X.ringCatSheaf

/-- The degree-`p` cohomology of a scheme module on an open subset, viewed as
a module over the section ring of that open subset. -/
abbrev moduleCohomologyAtOpen
    [HasInjectiveResolutions X.Modules]
    (U : Opens X) (F : X.Modules) (p : ℕ) :
    ModuleCat (RingedSpace.sectionsRingOnOpen X.toRingedSpace U) :=
  RingedSpace.moduleCohomologyAtOpen U F p

/-- Degree-`p` cohomology over the global section ring `Γ(X, ⊤)`,
functorially in the scheme module. -/
noncomputable abbrev cohomologyFunctor
    (X : Scheme.{u}) (p : ℕ) : X.Modules ⥤ ModuleCat Γ(X, ⊤) :=
  @RingedSpace.moduleCohomologyAtOpenFunctor X.toRingedSpace
    (hasInjectiveResolutions X) (⊤ : Opens X) p

/-- The degree-`p` cohomology of a scheme module, as a module over the global
section ring `Γ(X, ⊤)`.  This is the canonical object-level projection of
`cohomologyFunctor`. -/
noncomputable abbrev cohomology
    (F : X.Modules) (p : ℕ) : ModuleCat Γ(X, ⊤) :=
  (cohomologyFunctor X p).obj F

/-- Forgetting the section-ring module structure on scheme-module cohomology
recovers cohomology of the underlying additive sheaf. -/
theorem moduleCohomologyAtOpenForget_obj_eq_underlyingSheafCohomology
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [HasInjectiveResolutions X.Modules]
    (U : Opens X) (F : X.Modules) (p : ℕ) :
    (forget₂ (ModuleCat (RingedSpace.sectionsRingOnOpen X.toRingedSpace U))
      AddCommGrpCat.{u}).obj (moduleCohomologyAtOpen U F p) =
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H' p U := sorry

/-- Forgetting the global-section module structure on `cohomology F p`
recovers the ordinary cohomology object of the underlying additive sheaf. -/
theorem cohomologyForget_obj_eq
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (F : X.Modules) (p : ℕ) :
    (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat.{u}).obj (cohomology F p) =
      RingedSpace.moduleCohomology F p := sorry

end AlgebraicGeometry.Scheme.Modules
