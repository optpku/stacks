/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.Algebra.Module.FiniteLength.Determinant.OneDimensional
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Functoriality

/-!
# Functoriality of finite-length determinant spaces

This file bundles the action of module isomorphisms on determinant spaces as a functor between
cores.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace Module.FiniteLengthDeterminant

/-- The property of a module object that its underlying module has finite length. -/
def moduleProperty (R : Type u) [CommRing R] : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ IsFiniteLength R M

/-- Membership in `moduleProperty R` is finite length of the underlying module. -/
theorem mem_moduleProperty_iff (R : Type u) [CommRing R] (M : ModuleCat.{v} R) :
    moduleProperty R M ↔ IsFiniteLength R M := sorry

/-- The property of a vector-space object that its dimension is exactly one. -/
def lineProperty (κ : Type u) [Field κ] : ObjectProperty (ModuleCat.{v} κ) :=
  fun L ↦ Module.finrank κ L = 1

/-- Membership in `lineProperty κ` is the assertion that the underlying vector space has
dimension one. -/
theorem mem_lineProperty_iff (κ : Type u) [Field κ] (L : ModuleCat.{v} κ) :
    lineProperty κ L ↔ Module.finrank κ L = 1 := sorry

/-- The groupoid of finite-length `R`-module objects and their isomorphisms. -/
abbrev ModuleCore (R : Type u) [CommRing R] :=
  Core ((moduleProperty.{u, v} R).FullSubcategory)

/-- The groupoid of one-dimensional `κ`-vector-space objects and their isomorphisms. -/
abbrev LineCore (κ : Type u) [Field κ] :=
  Core ((lineProperty.{u, v} κ).FullSubcategory)

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Bundle the determinant space of a finite-length module as a one-dimensional residue-field
module object. -/
def line (X : (moduleProperty.{u, v} R).FullSubcategory) :
    (lineProperty.{u, max u v} (IsLocalRing.ResidueField R)).FullSubcategory :=
  ⟨ModuleCat.of (IsLocalRing.ResidueField R)
      (Module.FiniteLengthDeterminant R X.obj X.property),
    finrank_eq_one_of_isFiniteLength R X.obj X.property⟩

/-- The module underlying `line R X` is the determinant space of `X`. -/
theorem line_obj (X : (moduleProperty.{u, v} R).FullSubcategory) :
    (line R X).obj = ModuleCat.of (IsLocalRing.ResidueField R)
      (Module.FiniteLengthDeterminant R X.obj X.property) := sorry

/-- The determinant line of a finite-length module has dimension exactly one. -/
theorem line_finrank (X : (moduleProperty.{u, v} R).FullSubcategory) :
    Module.finrank (IsLocalRing.ResidueField R) (line R X).obj = 1 := sorry

/-- An isomorphism of finite-length module objects induces an isomorphism of their bundled
determinant lines. -/
def lineIso {X Y : (moduleProperty.{u, v} R).FullSubcategory} (e : X ≅ Y) :
    line R X ≅ line R Y :=
  ObjectProperty.isoMk
    (lineProperty (IsLocalRing.ResidueField R))
      (mapEquiv X.property Y.property
        ((moduleProperty R).ι.mapIso e).toLinearEquiv).toModuleIso

/-- The forward map of `lineIso` is the bundled determinant transport map. -/
theorem lineIso_hom {X Y : (moduleProperty.{u, v} R).FullSubcategory} (e : X ≅ Y) :
    (lineIso R e).hom.hom = ModuleCat.ofHom
      (mapEquiv X.property Y.property
        ((moduleProperty R).ι.mapIso e).toLinearEquiv).toLinearMap := sorry

/-- The identity isomorphism induces the identity determinant-line isomorphism. -/
theorem lineIso_refl (X : (moduleProperty.{u, v} R).FullSubcategory) :
    lineIso R (Iso.refl X) = Iso.refl (line R X) := sorry

/-- Determinant-line isomorphisms respect composition. -/
theorem lineIso_trans {X Y Z : (moduleProperty.{u, v} R).FullSubcategory}
    (e : X ≅ Y) (e' : Y ≅ Z) :
    lineIso R (e.trans e') = (lineIso R e).trans (lineIso R e') := sorry

/-- The object-level assignment used by the determinant functor. -/
def coreLine (X : ModuleCore.{u, v} R) :
    LineCore.{u, max u v} (IsLocalRing.ResidueField R) :=
  ⟨line R X.of⟩

/-- The morphism-level assignment used by the determinant functor. -/
def coreLineMap {X Y : ModuleCore.{u, v} R} (f : X ⟶ Y) :
    coreLine R X ⟶ coreLine R Y :=
  ⟨lineIso R f.iso⟩

/-- The determinant assignment preserves identity morphisms in the module core. -/
theorem coreLineMap_id (X : ModuleCore.{u, v} R) :
    coreLineMap R (𝟙 X) = 𝟙 (coreLine R X) := sorry

/-- The determinant assignment preserves composition in the module core. -/
theorem coreLineMap_comp {X Y Z : ModuleCore.{u, v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    coreLineMap R (f ≫ g) = coreLineMap R f ≫ coreLineMap R g := sorry

/-- The determinant functor from finite-length modules and isomorphisms to one-dimensional
residue-field vector spaces and isomorphisms. -/
def functor : ModuleCore.{u, v} R ⥤
    LineCore.{u, max u v} (IsLocalRing.ResidueField R) where
  obj := coreLine R
  map := coreLineMap R
  map_id := coreLineMap_id R
  map_comp := coreLineMap_comp R

/-- The object map of the determinant functor is the bundled determinant line. -/
theorem functor_obj (X : ModuleCore.{u, v} R) :
    (functor R).obj X = coreLine R X := sorry

/-- The morphism map of the determinant functor is induced by determinant transport. -/
theorem functor_map {X Y : ModuleCore.{u, v} R} (f : X ⟶ Y) :
    (functor R).map f = coreLineMap R f := sorry

end Module.FiniteLengthDeterminant
