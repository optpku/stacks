/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

/-! # Coefficient maps for morphisms to affine schemes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {A : CommRingCat.{u}}

/-- Restricting a morphism to an affine scheme to the chosen atlas gives a scheme morphism. -/
def affineAtlasHom {a : Spec A ⟶ S} (f : X ⟶ ofOver (Over.mk a)) :
    (chosenPresentation X).U ⟶ Over.mk a :=
  Yoneda.fullyFaithful.preimage
    ((chosenPresentation X).atlas ≫ f :
      yoneda.obj (chosenPresentation X).U ⟶ yoneda.obj (Over.mk a))

/-- The affine coefficient map on the atlas equalizes the two relation projections. -/
theorem affineGlobalSectionsMap_equalizes {a : Spec A ⟶ S}
    (f : X ⟶ ofOver (Over.mk a)) :
    ((Scheme.ΓSpecIso A).inv ≫ (affineAtlasHom f).left.appTop) ≫
        (chosenPresentation X).tAppTop =
      ((Scheme.ΓSpecIso A).inv ≫ (affineAtlasHom f).left.appTop) ≫
        (chosenPresentation X).sAppTop := sorry

/-- An affine-target morphism induces a coefficient homomorphism into global sections. -/
def affineGlobalSectionsMap {a : Spec A ⟶ S}
    (f : X ⟶ ofOver (Over.mk a)) : A ⟶ globalSectionsRing X :=
  equalizer.lift ((Scheme.ΓSpecIso A).inv ≫ (affineAtlasHom f).left.appTop)
    (affineGlobalSectionsMap_equalizes f)

/-- The coefficient homomorphism restricts to the actual scheme-level map on the atlas. -/
theorem affineGlobalSectionsMap_ι {a : Spec A ⟶ S}
    (f : X ⟶ ofOver (Over.mk a)) :
    affineGlobalSectionsMap f ≫ globalSectionsRing_ι X =
      (Scheme.ΓSpecIso A).inv ≫ (affineAtlasHom f).left.appTop := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
