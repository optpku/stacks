/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AtlasRinged
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Ringed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfComparison

/-!
# Ringed total sites of a simplicial algebraic space

The structure sheaves `𝒪_U` on `U_spaces,étale` and `𝒪_big,total` on
`(Spaces/U)_{fppf,total}` are the global-sections sheaves `V ↦ Γ(V, 𝒪_V)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.Atlas
open CategoryTheory.SimplicialObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- Ring-valued sheaves on the total spaces-étale site compose with `forget RingCat`. -/
instance hasSheafCompose_spacesEtaleTotalTopology :
    (spacesEtaleTotalTopology U).HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- Ring-valued sheaves on `(Spaces/U)_{fppf,total}` compose with `forget RingCat`. -/
instance hasSheafCompose_sliceTotalTopology_fppf :
    (sliceTotalTopology (fppfTopology S) U).HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- The ring presheaf on `SpacesEtale U` with value `Γ(V, 𝒪_V)` at an étale object
`V` over a stage of `U`. -/
def etaleTotalStructurePresheaf : (SpacesEtale U)ᵒᵖ ⥤ RingCat.{u} where
  obj Y := (forget₂ CommRingCat RingCat).obj (globalSectionsRing Y.unop.obj.left)
  map {Y Z} g := (forget₂ CommRingCat RingCat).map (globalSectionsRingMap g.unop.hom)
  map_id Y := by
    exact overEtaleStructurePresheaf_map_id Y.unop.obj.left
      (op (Over.mk (𝟙 Y.unop.obj.left)))
  map_comp {Y Z W} f g := by
    let h : Over.mk f.unop.hom ⟶ Over.mk (𝟙 Y.unop.obj.left) :=
      Over.homMk f.unop.hom (Category.comp_id f.unop.hom)
    let k : Over.mk (g.unop.hom ≫ f.unop.hom) ⟶ Over.mk f.unop.hom :=
      Over.homMk g.unop.hom rfl
    exact overEtaleStructurePresheaf_map_comp Y.unop.obj.left h.op k.op

/-- The value of `etaleTotalStructurePresheaf U` at `Y` is `Γ(Y.obj.left, 𝒪)`. -/
theorem etaleTotalStructurePresheaf_obj (Y : SpacesEtale U) :
    (etaleTotalStructurePresheaf U).obj (op Y) =
      (forget₂ CommRingCat RingCat).obj (globalSectionsRing Y.obj.left) :=
  rfl

/-- Restriction in `etaleTotalStructurePresheaf U` is `globalSectionsRingMap` of the
underlying morphism of algebraic spaces. -/
theorem etaleTotalStructurePresheaf_map {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    (etaleTotalStructurePresheaf U).map f.op =
      (forget₂ CommRingCat RingCat).map (globalSectionsRingMap f.hom) :=
  rfl

/-- The global-sections presheaf on `U_spaces,étale` is a sheaf. -/
theorem etaleTotalStructurePresheaf_isSheaf :
    Presheaf.IsSheaf (spacesEtaleTotalTopology U) (etaleTotalStructurePresheaf U) :=
  sorry

/-- The structure sheaf `𝒪_U` on the total spaces-étale site, with value
`V ↦ Γ(V, 𝒪_V)`. -/
def etaleTotalStructureSheaf : Sheaf (spacesEtaleTotalTopology U) RingCat.{u} :=
  ⟨etaleTotalStructurePresheaf U, etaleTotalStructurePresheaf_isSheaf U⟩

/-- On an étale object `Y` over a stage of `U`, `𝒪_U` has value `Γ(Y.obj.left, 𝒪)`. -/
theorem etaleTotalStructureSheaf_obj (Y : SpacesEtale U) :
    (etaleTotalStructureSheaf U).obj.obj (op Y) =
      (forget₂ CommRingCat RingCat).obj (globalSectionsRing Y.obj.left) :=
  rfl

/-- The ringed site `(Sh(U_spaces,étale), 𝒪_U)`. -/
abbrev etaleTotalRingedSite : RingedSite.{u + 1, u + 1, u} :=
  RingedSite.ofRingSheaf (spacesEtaleTotalTopology U) (etaleTotalStructureSheaf U)

/-- The structure sheaf of `etaleTotalRingedSite U` is `etaleTotalStructureSheaf U`. -/
theorem etaleTotalRingedSite_structureSheaf :
    (etaleTotalRingedSite U).structureSheaf = etaleTotalStructureSheaf U :=
  rfl

/-- The site topology of `etaleTotalRingedSite U` is `spacesEtaleTotalTopology U`. -/
theorem etaleTotalRingedSite_siteTopology :
    (etaleTotalRingedSite U).siteTopology = spacesEtaleTotalTopology U :=
  rfl

/-- Identity-degree inclusion of a stage is continuous for the spaces-étale topologies. -/
instance includeStage_isContinuous (n : SimplexCategoryᵒᵖ) :
    (@SpacesEtale.includeStage _ U n).IsContinuous
      (spacesEtaleTopology (U.obj n)) (spacesEtaleTotalTopology U) :=
  sorry

/-- Restriction of `𝒪_U` along `includeStage n` evaluates to `Γ(V, 𝒪_V)` on stage `n`. -/
theorem includeStage_etaleTotalStructureSheaf_obj (n : SimplexCategoryᵒᵖ)
    (V : spacesEtaleSite (U.obj n)) :
    (((@SpacesEtale.includeStage _ U n).sheafPushforwardContinuous RingCat.{u}
          (spacesEtaleTopology (U.obj n)) (spacesEtaleTotalTopology U)).obj
        (etaleTotalStructureSheaf U)).obj.obj (op V) =
      (forget₂ CommRingCat RingCat).obj (globalSectionsRing V.left) :=
  sorry

/-- Restriction along an identity total-site arrow is the identity on global sections. -/
theorem fppfTotalStructurePresheaf_map_id (Y : (sliceTotalSite U)ᵒᵖ) :
    (forget₂ CommRingCat RingCat).map
        (globalSectionsRingMap (𝟙 Y).unop.fiber.left) =
      𝟙 ((forget₂ CommRingCat RingCat).obj (globalSectionsRing Y.unop.fiber.left)) := by
  sorry

/-- Restriction along a composite total-site arrow is the composite of the restrictions. -/
theorem fppfTotalStructurePresheaf_map_comp
    {Y Z W : (sliceTotalSite U)ᵒᵖ} (g : Y ⟶ Z) (h : Z ⟶ W) :
    (forget₂ CommRingCat RingCat).map
        (globalSectionsRingMap (g ≫ h).unop.fiber.left) =
      (forget₂ CommRingCat RingCat).map (globalSectionsRingMap g.unop.fiber.left) ≫
        (forget₂ CommRingCat RingCat).map (globalSectionsRingMap h.unop.fiber.left) := by
  sorry

/-- The ring presheaf on `(Spaces/U)_{fppf,total}` with value `Γ(V, 𝒪_V)` at an object
`V / U_n`. -/
def fppfTotalStructurePresheaf : (sliceTotalSite U)ᵒᵖ ⥤ RingCat.{u} where
  obj Y := (forget₂ CommRingCat RingCat).obj (globalSectionsRing Y.unop.fiber.left)
  map {Y Z} g :=
    (forget₂ CommRingCat RingCat).map (globalSectionsRingMap g.unop.fiber.left)
  map_id := fppfTotalStructurePresheaf_map_id U
  map_comp := fppfTotalStructurePresheaf_map_comp U

/-- The value of `fppfTotalStructurePresheaf U` at `Y` is `Γ(Y.fiber.left, 𝒪)`. -/
theorem fppfTotalStructurePresheaf_obj (Y : sliceTotalSite U) :
    (fppfTotalStructurePresheaf U).obj (op Y) =
      (forget₂ CommRingCat RingCat).obj (globalSectionsRing Y.fiber.left) :=
  rfl

/-- Restriction in `fppfTotalStructurePresheaf U` is `globalSectionsRingMap` of the
underlying morphism of algebraic spaces. -/
theorem fppfTotalStructurePresheaf_map {Y Z : sliceTotalSite U} (f : Y ⟶ Z) :
    (fppfTotalStructurePresheaf U).map f.op =
      (forget₂ CommRingCat RingCat).map (globalSectionsRingMap f.fiber.left) :=
  rfl

/-- The global-sections presheaf on `(Spaces/U)_{fppf,total}` is a sheaf. -/
theorem fppfTotalStructurePresheaf_isSheaf :
    Presheaf.IsSheaf (sliceTotalTopology (fppfTopology S) U) (fppfTotalStructurePresheaf U) :=
  sorry

/-- The structure sheaf `𝒪_big,total` on `(Spaces/U)_{fppf,total}`, with value
`V ↦ Γ(V, 𝒪_V)`. -/
def fppfTotalStructureSheaf :
    Sheaf (sliceTotalTopology (fppfTopology S) U) RingCat.{u} :=
  ⟨fppfTotalStructurePresheaf U, fppfTotalStructurePresheaf_isSheaf U⟩

/-- On an object `Y` of `(Spaces/U)_{fppf,total}`, `𝒪_big,total` has value
`Γ(Y.fiber.left, 𝒪)`. -/
theorem fppfTotalStructureSheaf_obj (Y : sliceTotalSite U) :
    (fppfTotalStructureSheaf U).obj.obj (op Y) =
      (forget₂ CommRingCat RingCat).obj (globalSectionsRing Y.fiber.left) :=
  rfl

/-- The ringed site `(Sh((Spaces/U)_{fppf,total}), 𝒪_big,total)`. -/
abbrev fppfTotalRingedSite : RingedSite.{u + 1, u + 1, u} :=
  RingedSite.ofRingSheaf (sliceTotalTopology (fppfTopology S) U) (fppfTotalStructureSheaf U)

/-- The structure sheaf of `fppfTotalRingedSite U` is `fppfTotalStructureSheaf U`. -/
theorem fppfTotalRingedSite_structureSheaf :
    (fppfTotalRingedSite U).structureSheaf = fppfTotalStructureSheaf U :=
  rfl

/-- The site topology of `fppfTotalRingedSite U` is the fppf total topology. -/
theorem fppfTotalRingedSite_siteTopology :
    (fppfTotalRingedSite U).siteTopology = sliceTotalTopology (fppfTopology S) U :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
