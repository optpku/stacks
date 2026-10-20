/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Derived.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally given derived module sheaves and their global solutions
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe z u v w uB vB

namespace SheafOfModules.Derived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (O : Sheaf J RingCat.{w})
variable [abelianOver : ∀ U : C, Abelian (SheafOfModules.{z} (O.over U))]

/-- Derived module sheaves indexed by a functor, with invertible restriction transitions
satisfying the composition cocycle. -/
@[stacks 0DC9]
structure LocallyGiven (B : Type uB) [Category.{vB} B] where
  /-- The functor indexing the local objects on the site. -/
  u : B ⥤ C
  /-- The derived module sheaf attached to each indexing object. -/
  obj (U : B) : Derived.{z} (O.over (u.obj U))
  /-- The invertible transition from a restricted local object to the next local object. -/
  iso {V U : B} (a : V ⟶ U) :
    (restrictionDerived O (u.map a)).obj (obj U) ≅ obj V
  /-- The composition cocycle, transported by the canonical restriction comparison. -/
  iso_comp {W V U : B} (a : V ⟶ U) (b : W ⟶ V) :
      ((restrictionCompIso O (u.map a) (u.map b)).symm ≪≫
          restrictionDerivedCongr O (u.map_comp b a).symm).app (obj U) ≪≫
        iso (b ≫ a) =
      (restrictionDerived O (u.map b)).mapIso (iso a) ≪≫ iso b

variable {B : Type uB} [Category.{vB} B]

/-- The transition isomorphisms of a locally given datum satisfy the transported cocycle. -/
theorem spec (D : LocallyGiven O B) {W V U : B} (a : V ⟶ U) (b : W ⟶ V) :
    ((restrictionCompIso O (D.u.map a) (D.u.map b)).symm ≪≫
        restrictionDerivedCongr O (D.u.map_comp b a).symm).app (D.obj U) ≪≫
      D.iso (b ≫ a) =
    (restrictionDerived O (D.u.map b)).mapIso (D.iso a) ≪≫ D.iso b := sorry

variable [abelian : Abelian (SheafOfModules.{z} O)]

/-- The canonical iterated restriction comparisons of a global object satisfy the cocycle. -/
theorem ofGlobal_iso_comp (E : Derived.{z} O) {W V U : C} (a : V ⟶ U) (b : W ⟶ V) :
    ((restrictionCompIso O a b).symm ≪≫
        restrictionDerivedCongr O ((𝟭 C).map_comp b a).symm).app
          ((localizedRestrictionDerived O U).obj E) ≪≫
      (restrictionDerivedIteratedIso O (b ≫ a)).app E =
    (restrictionDerived O b).mapIso ((restrictionDerivedIteratedIso O a).app E) ≪≫
      (restrictionDerivedIteratedIso O b).app E := sorry

/-- A global derived module sheaf gives local restrictions indexed by the identity functor,
with the canonical iterated restriction comparisons as transitions. -/
def ofGlobal (E : Derived.{z} O) : LocallyGiven O C where
  u := 𝟭 C
  obj U := (localizedRestrictionDerived O U).obj E
  iso a := (restrictionDerivedIteratedIso O a).app E
  iso_comp := ofGlobal_iso_comp O E

/-- The datum of a global object has its actual local restrictions and canonical transitions. -/
theorem ofGlobal_spec (E : Derived.{z} O) :
    (∀ U : C, (ofGlobal O E).obj U = (localizedRestrictionDerived O U).obj E) ∧
      (∀ {V U : C} (a : V ⟶ U),
        (ofGlobal O E).iso a = (restrictionDerivedIteratedIso O a).app E) := sorry

/-- On an identity arrow the transition of a global datum is the canonical comparison. -/
theorem ofGlobal_iso_id (E : Derived.{z} O) (U : C) :
    ((ofGlobal O E).iso (𝟙 U)).hom =
      (restrictionDerivedIteratedIso O (𝟙 U)).hom.app E := sorry

/-- A solution consists of a global derived module sheaf and local identifications compatible
with the given invertible transitions. -/
structure Solution (D : LocallyGiven O B) where
  /-- The global derived module sheaf. -/
  obj : Derived.{z} O
  /-- The identification of each restriction of the global object with the given local object. -/
  iso (U : B) : (localizedRestrictionDerived O (D.u.obj U)).obj obj ≅ D.obj U
  /-- Compatibility of the identifications with the given transition isomorphisms. -/
  iso_comp {V U : B} (a : V ⟶ U) :
      (restrictionDerived O (D.u.map a)).map (iso U).hom ≫ (D.iso a).hom =
        (restrictionDerivedIteratedIso O (D.u.map a)).hom.app obj ≫ (iso V).hom

namespace Solution

/-- Identity identifications of restrictions satisfy the solution compatibility equation. -/
theorem ofGlobal_iso_comp (E : Derived.{z} O) {V U : C} (a : V ⟶ U) :
    (restrictionDerived O a).map (Iso.refl ((localizedRestrictionDerived O U).obj E)).hom ≫
        ((ofGlobal O E).iso a).hom =
      (restrictionDerivedIteratedIso O a).hom.app E ≫
        (Iso.refl ((localizedRestrictionDerived O V).obj E)).hom := sorry

/-- The original global object with identity identifications solves its restriction datum. -/
def ofGlobal (E : Derived.{z} O) : Solution O (Derived.ofGlobal O E) where
  obj := E
  iso U := Iso.refl ((localizedRestrictionDerived O U).obj E)
  iso_comp := ofGlobal_iso_comp O E

/-- The tautological solution retains the global object and identity local identifications. -/
theorem ofGlobal_spec (E : Derived.{z} O) :
    (ofGlobal O E).obj = E ∧
      (∀ U : C, (ofGlobal O E).iso U = Iso.refl ((localizedRestrictionDerived O U).obj E)) := sorry

/-- The global object of the tautological solution is the original object. -/
theorem ofGlobal_obj (E : Derived.{z} O) : (ofGlobal O E).obj = E := sorry

end Solution
end SheafOfModules.Derived
