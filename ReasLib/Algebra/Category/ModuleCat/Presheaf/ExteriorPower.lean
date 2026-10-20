/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.RestrictScalars
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing

/-!
# Exterior powers of module presheaves

For a presheaf of commutative rings `𝒪`, this file constructs the sectionwise exterior-power
presheaf of a presheaf of modules over the underlying ring presheaf.  Restriction maps are built
from `ModuleCat.exteriorPower.mapRestrictScalars`, so no ambient scalar action has to be replaced.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace PresheafOfModules.ExteriorPower

variable {C : Type u} [Category.{v} C]
variable (𝒪 : CategoryTheory.Functor Cᵒᵖ CommRingCat.{w})

/-- The underlying ring-valued presheaf of `𝒪`. -/
abbrev RingPresheaf := CategoryTheory.Presheaf.ringPresheafOfComm 𝒪

/-- A section module, viewed over the corresponding commutative section ring. -/
abbrev sectionObj (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    ModuleCat (𝒪.obj U) :=
  F.obj U

/-- A module-presheaf restriction map, viewed along the corresponding commutative ring map. -/
abbrev restriction (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    sectionObj 𝒪 F U ⟶
      (ModuleCat.restrictScalars (𝒪.map i).hom).obj (sectionObj 𝒪 F V) :=
  F.map i

/-- The degree-`n` exterior power of the module of sections over one object of the site. -/
abbrev obj (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (n : ℕ) (U : Cᵒᵖ) :
    ModuleCat (𝒪.obj U) :=
  (sectionObj 𝒪 F U).exteriorPower n

/-- The restriction morphism on sectionwise degree-`n` exterior powers. -/
noncomputable def map (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (n : ℕ)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    obj 𝒪 F n U ⟶
      (ModuleCat.restrictScalars (𝒪.map i).hom).obj (obj 𝒪 F n V) :=
  ModuleCat.exteriorPower.mapRestrictScalars (𝒪.map i).hom (restriction 𝒪 F i) n

/-- The exterior-power restriction morphism acts entrywise on alternating generators. -/
@[simp]
theorem map_mk (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (n : ℕ)
    {U V : Cᵒᵖ} (i : U ⟶ V) (m : Fin n → sectionObj 𝒪 F U) :
    map 𝒪 F n i
        (ModuleCat.exteriorPower.mk (R := 𝒪.obj U) (M := sectionObj 𝒪 F U) m) =
      ModuleCat.exteriorPower.mk (R := 𝒪.obj V) (M := sectionObj 𝒪 F V)
        (fun j ↦ restriction 𝒪 F i (m j)) := sorry

/-- The sectionwise exterior-power restriction morphism preserves identity morphisms. -/
theorem map_id (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (n : ℕ) (U : Cᵒᵖ) :
    map 𝒪 F n (𝟙 U) =
      (ModuleCat.restrictScalarsId' (𝒪.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (𝒪.map_id U))).inv.app (obj 𝒪 F n U) := sorry

/-- The sectionwise exterior-power restriction morphism preserves composition. -/
theorem map_comp (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (n : ℕ)
    {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    map 𝒪 F n (i ≫ j) =
      map 𝒪 F n i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map (map 𝒪 F n j) ≫
        (ModuleCat.restrictScalarsComp' (𝒪.map i).hom (𝒪.map j).hom
          (𝒪.map (i ≫ j)).hom (congrArg CommRingCat.Hom.hom (𝒪.map_comp i j))).inv.app
          (obj 𝒪 F n W) := sorry

set_option maxHeartbeats 800000 in
/-- The sectionwise degree-`n` exterior-power presheaf of `F`. -/
noncomputable def presheaf (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (n : ℕ) :
    PresheafOfModules.{max w z} (RingPresheaf 𝒪) where
  obj U := obj 𝒪 F n U
  map i := map 𝒪 F n i
  map_id U := map_id 𝒪 F n U
  map_comp i j := map_comp 𝒪 F n i j

/-- A component of a module-presheaf morphism, viewed over the commutative section ring. -/
abbrev homApp {F G : PresheafOfModules.{max w z} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (U : Cᵒᵖ) : sectionObj 𝒪 F U ⟶ sectionObj 𝒪 G U :=
  f.app U

/-- Naturality of the sectionwise exterior-power maps induced by a morphism of module
presheaves. -/
theorem hom_naturality {F G : PresheafOfModules.{max w z} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (n : ℕ) {U V : Cᵒᵖ} (i : U ⟶ V) :
    map 𝒪 F n i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map
          (ModuleCat.exteriorPower.map (homApp 𝒪 f V) n) =
      ModuleCat.exteriorPower.map (homApp 𝒪 f U) n ≫ map 𝒪 G n i := sorry

/-- The morphism on sectionwise exterior-power presheaves induced by a morphism of module
presheaves. -/
noncomputable def hom {F G : PresheafOfModules.{max w z} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (n : ℕ) : presheaf 𝒪 F n ⟶ presheaf 𝒪 G n where
  app U := ModuleCat.exteriorPower.map (homApp 𝒪 f U) n
  naturality i := hom_naturality 𝒪 f n i

/-- The induced morphism of exterior-power presheaves acts entrywise on alternating
generators. -/
@[simp]
theorem hom_app_mk {F G : PresheafOfModules.{max w z} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (n : ℕ) (U : Cᵒᵖ) (m : Fin n → sectionObj 𝒪 F U) :
    (hom 𝒪 f n).app U
        (ModuleCat.exteriorPower.mk (R := 𝒪.obj U) (M := sectionObj 𝒪 F U) m) =
      ModuleCat.exteriorPower.mk (R := 𝒪.obj U) (M := sectionObj 𝒪 G U)
        (fun j ↦ homApp 𝒪 f U (m j)) := sorry

/-- The exterior-power construction sends an identity morphism to an identity morphism. -/
theorem hom_id (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (n : ℕ) :
    hom 𝒪 (𝟙 F) n = 𝟙 (presheaf 𝒪 F n) := sorry

/-- The exterior-power construction preserves composition of module-presheaf morphisms. -/
theorem hom_comp {F G H : PresheafOfModules.{max w z} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (g : G ⟶ H) (n : ℕ) :
    hom 𝒪 (f ≫ g) n = hom 𝒪 f n ≫ hom 𝒪 g n := sorry

/-- The degree-`n` sectionwise exterior-power endofunctor on module presheaves. -/
noncomputable def functor (n : ℕ) :
    CategoryTheory.Functor (PresheafOfModules.{max w z} (RingPresheaf 𝒪))
      (PresheafOfModules.{max w z} (RingPresheaf 𝒪)) where
  obj F := presheaf 𝒪 F n
  map f := hom 𝒪 f n
  map_id F := hom_id 𝒪 F n
  map_comp f g := hom_comp 𝒪 f g n

end PresheafOfModules.ExteriorPower
