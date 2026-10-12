/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Modules of sections on an open subset

This leaf owns the section ring on an open subset of a ringed space, the corresponding
module-valued evaluation functor, and restriction of scalars along the map induced by a morphism
of ringed spaces. Derived constructions belong in `Module.Derived.Sections`.
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

variable {X Y : RingedSpace.{u}}

/-- The ring of sections `Γ(U, 𝒪_X)` on an open subset `U` of a ringed space. -/
abbrev sectionsRingOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier) : CommRingCat :=
  X.presheaf.obj (op U)

/-- The module-valued evaluation functor `Γ(U, -)` on `𝒪_X`-modules. -/
abbrev moduleSectionsEvaluationFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    RingedSpace.Modules X ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)

/-- Evaluation of `𝒪_X`-modules on an open subset is additive. -/
instance moduleSectionsEvaluation_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsEvaluationFunctor X U).Additive := sorry

/-- Evaluation of `𝒪_X`-modules on an open subset preserves monomorphisms. -/
instance moduleSectionsEvaluation_preservesMonomorphisms
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsEvaluationFunctor X U).PreservesMonomorphisms := sorry

/-- Evaluation of module sheaves on an open subset preserves finite limits.  This is the
domain-abbreviation bridge to `SheafOfModules.Finite.evaluationPreservesFiniteLimits`. -/
noncomputable instance moduleSectionsEvaluation_preservesFiniteLimits
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleSectionsEvaluationFunctor X U) := sorry

/-- Evaluation on an open subset, after forgetting its section-module structure. -/
abbrev moduleSectionsAsAbelianFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  moduleSectionsEvaluationFunctor X U ⋙
    forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}

/-- The additive group of sections of a module sheaf on an open subset. -/
abbrev moduleSectionsOnOpen (M : X.Modules) (U : Opens X.carrier) : AddCommGrpCat :=
  AddCommGrpCat.of (M.val.obj (Opposite.op U))

/-- The map on sections over an open subset induced by a morphism of module
sheaves on a fixed ringed space. -/
abbrev moduleSectionsMapOnOpen {M N : X.Modules} (φ : M ⟶ N)
    (U : Opens X.carrier) :
    moduleSectionsOnOpen M U ⟶ moduleSectionsOnOpen N U :=
  AddCommGrpCat.ofHom ((φ.val.app (Opposite.op U)).hom)

namespace Modules.Hom

/-- A morphism of module sheaves on a ringed space, evaluated on sections over an open subset.
This is the ringed-space analogue of `Scheme.Modules.Hom.app`. -/
abbrev app {M N : X.Modules} (φ : M ⟶ N) (U : Opens X.carrier) :
    moduleSectionsOnOpen M U ⟶ moduleSectionsOnOpen N U :=
  moduleSectionsMapOnOpen φ U

end Modules.Hom

/-- The additive group of global sections of a module sheaf, evaluated on the
top open. -/
abbrev moduleGlobalSections (M : X.Modules) : AddCommGrpCat :=
  moduleSectionsOnOpen M ⊤

/-- The map on global sections induced by a morphism of module sheaves. -/
abbrev moduleGlobalSectionsMap {M N : X.Modules} (φ : M ⟶ N) :
    moduleGlobalSections M ⟶ moduleGlobalSections N :=
  moduleSectionsMapOnOpen φ ⊤

/-- The sections of a module sheaf on `U`, viewed as an `R`-module by restricting scalars along
an explicit ring map `R →+* Γ(U, 𝒪_X)`.  This is the canonical map-first owner;
the instance-based spelling below is only a compatibility view. -/
@[stacks 01BH "explicit section-scalar restriction"]
noncomputable abbrev moduleSectionsModuleOnOpenAlong
    (R : Type u) [CommRing R] (X : RingedSpace.{u}) (U : Opens X.carrier)
    (ρ : R →+* sectionsRingOnOpen X U) (M : X.Modules) :
    Module R (M.val.obj (op U)) :=
  Module.compHom (M.val.obj (op U)) ρ

/-- The sections of a module sheaf on `U`, viewed as an `R`-module by restricting scalars along
a chosen `R`-algebra structure on `Γ(U, 𝒪_X)`. -/
noncomputable abbrev moduleSectionsModuleOnOpen
    (R : Type u) [CommRing R] (X : RingedSpace.{u}) (U : Opens X.carrier)
    [Algebra R (sectionsRingOnOpen X U)]
    (M : X.Modules) : Module R (M.val.obj (op U)) :=
  moduleSectionsModuleOnOpenAlong R X U (algebraMap R (sectionsRingOnOpen X U)) M

/-- The global sections of a module sheaf, viewed as an `R`-module by restricting scalars along
a chosen `R`-algebra structure on the global section ring of the ringed space. -/
noncomputable abbrev moduleGlobalSectionsModule
    (R : Type u) [CommRing R] (X : RingedSpace.{u})
    [Algebra R (sectionsRingOnOpen X (⊤ : Opens X.carrier))]
    (M : X.Modules) : Module R (M.val.obj (op (⊤ : Opens X.carrier))) :=
  moduleSectionsModuleOnOpen R X ⊤ M

/-- The abelian-group-valued sections functor on an open subset is additive. -/
instance moduleSectionsAsAbelianFunctor_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsAsAbelianFunctor X U).Additive := sorry

/-- Evaluation of module sheaves on an open subset preserves zero morphisms. -/
instance moduleSectionsEvaluation_preservesZeroMorphisms
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).PreservesZeroMorphisms :=
  sorry

/-- The map `Γ(V, 𝒪_Y) → Γ(f⁻¹(V), 𝒪_X)` induced by a morphism of ringed spaces. -/
abbrev sectionsMapOnOpen (f : X ⟶ Y) (V : Opens Y.carrier) :
    sectionsRingOnOpen Y V ⟶ sectionsRingOnOpen X (preimageOpen f V) :=
  f.hom.c.app (op V)

/-- Restriction of scalars along the section-ring map induced by `f` over `V`. -/
abbrev moduleSectionsRestrictionFunctor (f : X ⟶ Y) (V : Opens Y.carrier) :
    ModuleCat (sectionsRingOnOpen X (preimageOpen f V)) ⥤
      ModuleCat (sectionsRingOnOpen Y V) :=
  ModuleCat.restrictScalars (sectionsMapOnOpen f V).hom

section

variable (X : RingedSpace.{u}) (U : Opens X.carrier)


end

end AlgebraicGeometry.RingedSpace
