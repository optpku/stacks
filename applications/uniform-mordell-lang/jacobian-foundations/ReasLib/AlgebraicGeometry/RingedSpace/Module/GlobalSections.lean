module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SectionScalars
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic

/-!
# Module-valued global sections on ringed spaces

This leaf owns the global-sections ring of a ringed space and the ordinary module-valued
global-sections functor. Derived global sections belong in `Module.Derived.GlobalSections`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The ring of global sections `Γ(X, 𝒪_X)` of a ringed space. -/
abbrev globalSectionsRing (X : RingedSpace.{u}) : CommRingCat :=
  SheafedSpace.Γ.obj (op X)

/-- The global-sections functor on `𝒪_X`-modules. -/
abbrev moduleGlobalSectionsFunctor (X : RingedSpace.{u}) :
    X.Modules ⥤ ModuleCat (globalSectionsRing X) :=
  SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op (⊤ : Opens X.carrier))

/-- The canonical `Γ(X, 𝒪_X)`-module structure on the top-open value of an
`𝒪_X`-module sheaf.  This bridges the commutative structure sheaf to the underlying ring sheaf
used by `SheafOfModules`, so downstream section constructions need no local scalar instance. -/
@[stacks 01BH "global-section module scalar structure"]
noncomputable instance instModuleGlobalSections (M : X.Modules) :
    Module (globalSectionsRing X) (M.val.presheaf.obj (op ⊤)) :=
  SheafOfModules.RingedSite.sectionModule (𝟙 X.sheaf) M (op ⊤)

/-- Global sections of a module sheaf with scalars restricted along an explicit
ring map `R →+* Γ(X, 𝒪_X)`. -/
@[stacks 01BH "global-section scalars along an explicit map"]
noncomputable abbrev moduleGlobalSectionsModuleAlong
    (R : Type u) [CommRing R] (X : RingedSpace.{u})
    (α : R →+* globalSectionsRing X) (M : X.Modules) :
    Module R (M.val.presheaf.obj (op ⊤)) :=
  Module.compHom (M.val.presheaf.obj (op ⊤)) α

/-- The global-sections functor on `𝒪_X`-modules is additive. -/
instance moduleGlobalSectionsFunctor_additive (X : RingedSpace.{u}) :
    (moduleGlobalSectionsFunctor X).Additive := sorry

/-- The global-sections functor on `𝒪_X`-modules preserves monomorphisms.

This is the terminal-open specialization of
`moduleSectionsEvaluation_preservesMonomorphisms`; it is kept as an instance because the
abbreviated global-sections functor is a frequent downstream input. -/
instance moduleGlobalSectionsFunctor_preservesMonomorphisms (X : RingedSpace.{u}) :
    (moduleGlobalSectionsFunctor X).PreservesMonomorphisms := sorry

/-- The global-sections functor on `𝒪_X`-modules preserves finite limits.  This is the
terminal-open bridge to `moduleSectionsEvaluation_preservesFiniteLimits`. -/
noncomputable instance moduleGlobalSectionsFunctor_preservesFiniteLimits
    (X : RingedSpace.{u}) : PreservesFiniteLimits (moduleGlobalSectionsFunctor X) := sorry


section

variable (X : RingedSpace.{u}) (M : X.Modules)


end


end AlgebraicGeometry.RingedSpace
