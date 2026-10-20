module

public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Monoidal.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat objects in `ModuleCat`

This file identifies algebraic flatness of a module with flatness of the corresponding object in
the monoidal category of modules.  The categorical predicate remains the shared owner; the
algebraic predicate is its concrete `ModuleCat` view.

@stack 064K
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The object property on `ModuleCat R` defined by algebraic flatness over `R`. -/
@[stacks 0D2I "flat module object property"]
def flat (R : Type u) [CommRing R] : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ Module.Flat R M

/-- The full subcategory of algebraically flat `R`-modules. -/
@[stacks 0D2I "category of flat modules"]
abbrev Flat (R : Type u) [CommRing R] := (flat.{u, v} R).FullSubcategory

/-- Algebraic flatness is closed under isomorphisms in `ModuleCat`. -/
@[stacks 0D2I "flat modules are closed under isomorphisms"]
instance flat.isClosedUnderIsomorphisms (R : Type u) [CommRing R] :
    (flat.{u, v} R).IsClosedUnderIsomorphisms := sorry

/-- For a bundled module, categorical monoidal flatness is equivalent to algebraic module
flatness. -/
@[stacks 064K "module-flat bridge"]
theorem isFlat_iff_module_flat (M : ModuleCat.{u} R) :
    MonoidalCategory.IsFlat M ↔ Module.Flat R M := sorry

/-- An algebraically flat bundled module is flat as an object of its monoidal category. -/
instance isFlat_of_moduleFlat (M : ModuleCat.{u} R) [Module.Flat R M] :
    MonoidalCategory.IsFlat M := sorry

/- The following two declarations are categorical adapters, not a second owner of flatness. -/

/-- Algebraic flatness of a bundled module is transported across a `ModuleCat` isomorphism.

The isomorphism is an explicit argument because it is chosen comparison data, while the
flatness predicate itself remains the algebraic `Module.Flat` owner. -/
@[stacks 064K "module-flat transport across an isomorphism"]
theorem moduleFlat_of_iso {M N : ModuleCat.{v} R} (e : M ≅ N) [Module.Flat R M] :
    Module.Flat R N := sorry

/-- Algebraic flatness is invariant under a `ModuleCat` isomorphism. -/
@[stacks 064K "module-flat isomorphism invariance"]
theorem moduleFlat_iff_of_iso {M N : ModuleCat.{v} R} (e : M ≅ N) :
    Module.Flat R M ↔ Module.Flat R N := sorry


end ModuleCat
