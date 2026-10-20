/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigStructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AtlasRinged
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Comparison of the two global-section presentations -/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Big

variable {S : Scheme.{u}}

/-- The presenting scheme, regarded as an object of the small étale site. -/
private def atlasChart (X : AlgebraicSpace S) : smallEtaleSite X :=
  smallEtaleSite.mk (chosenPresentation X).atlas
    ((SmallEtale.etale_iff _).mpr (chosenPresentation X).atlas_etale)

/-- The arrow from the presenting scheme to the terminal spaces-étale object. -/
private def atlasChartToSelf (X : AlgebraicSpace S) :
    (smallEtaleToSpaces X).obj (atlasChart X) ⟶ spacesEtaleSite.self X :=
  MorphismProperty.Over.homMk (chosenPresentation X).atlas
    (Category.comp_id _) trivial

/-- Restriction of a global section to the presenting scheme. -/
private def gammaToAtlas (X : AlgebraicSpace S) :
    gamma X ⟶ (forget₂ CommRingCat RingCat).obj Γ((chosenPresentation X).U.left, ⊤) :=
  EtaleRingedTopos.ringExtensionEvaluation X (AlgebraicSpace.structureSheaf X) (atlasChartToSelf X)

/-- A global function restricts to a scheme chart by its canonical map to the spectrum of global sections. -/
private def globalSectionsToChart (X : AlgebraicSpace S)
    (a : StructuredArrow (op (spacesEtaleSite.self X)) (smallEtaleToSpaces X).op) :
    (forget₂ CommRingCat RingCat).obj (globalSectionsRing X) ⟶
      (AlgebraicSpace.structureSheaf X).obj.obj a.right :=
  (forget₂ CommRingCat RingCat).map
    ((Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
      ((Yoneda.fullyFaithful.preimage
        (a.right.unop.hom ≫ toSpecGamma X)).left ≫ specGamma_fst X).appTop)

/-- Atlas restriction equalizes the kernel pair, and restrictions of a global function to scheme charts are natural. -/
theorem gammaGlobalSectionsHom_equalizes (X : AlgebraicSpace S) :
    (gammaToAtlas X ≫ (forget₂ CommRingCat RingCat).map (chosenPresentation X).tAppTop =
      gammaToAtlas X ≫ (forget₂ CommRingCat RingCat).map (chosenPresentation X).sAppTop) ∧
    ∀ (a b : StructuredArrow (op (spacesEtaleSite.self X)) (smallEtaleToSpaces X).op)
      (f : a ⟶ b),
      globalSectionsToChart X a ≫
        (StructuredArrow.proj (op (spacesEtaleSite.self X)) (smallEtaleToSpaces X).op ⋙
          (AlgebraicSpace.structureSheaf X).obj).map f = globalSectionsToChart X b := by
  sorry

/-- Atlas restriction gives a ring map into the kernel-pair equalizer of global sections. -/
def gammaGlobalSectionsHom (X : AlgebraicSpace S) :
    gamma X ⟶ (forget₂ CommRingCat RingCat).obj (globalSectionsRing X) :=
  equalizer.lift (gammaToAtlas X) (gammaGlobalSectionsHom_equalizes X).1 ≫
    (PreservesEqualizer.iso (forget₂ CommRingCat RingCat)
      (chosenPresentation X).tAppTop (chosenPresentation X).sAppTop).inv

/-- The reverse comparison is the unique ring-valued extension of the restrictions to all scheme charts. -/
def gammaGlobalSectionsInv (X : AlgebraicSpace S) :
    (forget₂ CommRingCat RingCat).obj (globalSectionsRing X) ⟶ gamma X :=
  EtaleRingedTopos.ringExtensionLift X (AlgebraicSpace.structureSheaf X) (spacesEtaleSite.self X)
    { pt := (forget₂ CommRingCat RingCat).obj (globalSectionsRing X)
      π :=
        { app := globalSectionsToChart X
          naturality := fun a b f ↦ by
            exact (Category.id_comp (globalSectionsToChart X b)).trans
              ((gammaGlobalSectionsHom_equalizes X).2 a b f).symm } }

/-- Restriction to the atlas followed by descent recovers the original global section. -/
theorem gammaGlobalSectionsHom_inv_id (X : AlgebraicSpace S) :
    gammaGlobalSectionsHom X ≫ gammaGlobalSectionsInv X = 𝟙 (gamma X) := by
  sorry

/-- Descent followed by restriction recovers the original element of the atlas equalizer. -/
theorem gammaGlobalSectionsInv_hom_id (X : AlgebraicSpace S) :
    gammaGlobalSectionsInv X ≫ gammaGlobalSectionsHom X =
      𝟙 ((forget₂ CommRingCat RingCat).obj (globalSectionsRing X)) := by
  sorry

/-- Global sections of the spaces-étale structure sheaf identify with the atlas kernel-pair equalizer. -/
def gammaGlobalSectionsIso (X : AlgebraicSpace S) :
    gamma X ≅ (forget₂ CommRingCat RingCat).obj (globalSectionsRing X) where
  hom := gammaGlobalSectionsHom X
  inv := gammaGlobalSectionsInv X
  hom_inv_id := gammaGlobalSectionsHom_inv_id X
  inv_hom_id := gammaGlobalSectionsInv_hom_id X

/-- The global-section comparison commutes with pullback along every morphism of algebraic spaces. -/
theorem gammaGlobalSectionsIso_naturality {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    gammaMap f ≫ (gammaGlobalSectionsIso Y).hom =
      (gammaGlobalSectionsIso X).hom ≫
        (forget₂ CommRingCat RingCat).map (Atlas.globalSectionsRingMap f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.Big
