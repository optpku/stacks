/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent

/-!
# Étale module inverse image along a 1-morphism of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` induces
`f^* = f⁻¹` on étale modules by `SheafOfModules.pushforward` along the
coefficient map `𝒪_X ⟶ f⁻¹ 𝒪_Y`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

variable {X Y : GroupoidsOver S}

/-- The canonical coefficient morphism `𝒪_X ⟶ f⁻¹ 𝒪_Y`. -/
abbrev etaleStructureSheafMap (f : X ⟶ Y) :
    etaleStructureSheaf X ⟶
      ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleStructureSheaf Y) :=
  etaleSiteHom_structureSheafMap f

/-- The coefficient morphism `𝒪_X ⟶ f⁻¹ 𝒪_Y` is an isomorphism, so `f^* = f⁻¹`. -/
theorem etaleStructureSheafMap_isIso (f : X ⟶ Y) :
    IsIso (etaleStructureSheafMap f) :=
  etaleSiteHom_structureSheafMap_isIso f

/-- The pullback functor `f^* = f⁻¹ : Mod(Y_étale, 𝒪_Y) ⟶ Mod(X_étale, 𝒪_X)`. -/
abbrev moduleInverseImage (f : X ⟶ Y) : etaleModules Y ⥤ etaleModules X :=
  etaleModuleInverseImage f

#check (commEtaleStructureSheafIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    ((toFunctor f).sheafPushforwardContinuous CommRingCat.{u}
      X.etaleTopology Y.etaleTopology).obj (commEtaleStructureSheaf Y) ≅
        commEtaleStructureSheaf X)

#check (inverseImageEtaleStructureSheafIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    CategoryTheory.Sheaf.ringSheafOfComm.{u, u + 1, u}
      (((toFunctor f).sheafPushforwardContinuous CommRingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (commEtaleStructureSheaf Y)) ≅
      ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleStructureSheaf Y))

#check (etaleSiteHom_structureSheafMap :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    etaleStructureSheaf X ⟶
      ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleStructureSheaf Y))

#check (etaleSiteHom_structureSheafMap_isIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    IsIso (etaleSiteHom_structureSheafMap f))

#check (etaleModuleInverseImage :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    etaleModules Y ⥤ etaleModules X)

end AlgebraicGeometry.GroupoidsOver
