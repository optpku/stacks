/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import stacks_project.Chap65.Lemma_65_9_1
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation.Descent

/-!
# Morphisms from an algebraic space to an affine scheme

The classification and presentation descent are provided by their mathematical owners.
The public imports and typed checks preserve the chapter-facing interface.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (specZ : Scheme.{u})

#check (specZ_eq : specZ.{u} = Spec (.of (ULift.{u} ℤ)))

#check (overSpecZ : ∀ (T : Scheme.{u}),
  Over specZ)

#check (overSpecZ_left : ∀ (T : Scheme.{u}),
  (overSpecZ T).left = T)

#check (overSpecZ_hom : ∀ (T : Scheme.{u}),
  (overSpecZ T).hom = specULiftZIsTerminal.from T)

namespace Presentation

#check (homDesc : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X)
    {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g),
  X ⟶ Y)

#check (homDesc_comp_atlas : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X)
    {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g),
  P.atlas ≫ homDesc P g h = (g : yoneda.obj P.U ⟶ Y.functorOfPoints))

end Presentation

namespace GlobalSections

#check (atlasOverHom : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}}
    (f : X ⟶ ofOver (overSpecZ T)),
  (chosenPresentation X).U ⟶ overSpecZ T)

#check (atlasOverHom_map : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}}
    (f : X ⟶ ofOver (overSpecZ T)),
  yoneda.map (atlasOverHom f) =
      ((chosenPresentation X).atlas ≫ f :
        yoneda.obj (chosenPresentation X).U ⟶ yoneda.obj (overSpecZ T)))

#check (globalSectionsMap_equalizes : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}}
    (f : X ⟶ ofOver (overSpecZ T)),
  (atlasOverHom f).left.appTop ≫ (chosenPresentation X).tAppTop =
      (atlasOverHom f).left.appTop ≫ (chosenPresentation X).sAppTop)

#check (globalSectionsMap : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}}
    (f : X ⟶ ofOver (overSpecZ T)),
  Γ(T, ⊤) ⟶ globalSectionsRing X)

#check (globalSectionsMap_eq_appTop : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}}
    (f : X ⟶ ofOver (overSpecZ T)),
  globalSectionsMap f ≫ globalSectionsRing_ι X = (atlasOverHom f).left.appTop)

#check (schemeHomMk : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X),
  (chosenPresentation X).U.left ⟶ (overSpecZ T).left)

#check (schemeHomMk_w : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X),
  schemeHomMk φ ≫ (overSpecZ T).hom = (chosenPresentation X).U.hom)

#check (overHomMk : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X),
  (chosenPresentation X).U ⟶ overSpecZ T)

#check (overHomMk_left : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X),
  (overHomMk φ).left = schemeHomMk φ)

#check (homMk_equalizes : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X),
  ofOverMap (chosenPresentation X).R.t ≫ ofOverMap (overHomMk φ) =
      ofOverMap (chosenPresentation X).R.s ≫ ofOverMap (overHomMk φ))

#check (homMk : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X),
  X ⟶ ofOver (overSpecZ T))

#check (homMk_globalSectionsMap : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (f : X ⟶ ofOver (overSpecZ T)),
  homMk (globalSectionsMap f) = f)

#check (globalSectionsMap_homMk : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X),
  globalSectionsMap (homMk φ) = φ)

#check (homEquivAffine : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T],
  (X ⟶ ofOver (overSpecZ T)) ≃ (Γ(T, ⊤) ⟶ globalSectionsRing X))

#check (homEquivAffine_apply : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (f : X ⟶ ofOver (overSpecZ T)),
  homEquivAffine f = globalSectionsMap f)

#check (homEquivAffine_symm_apply : ∀ {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X),
  homEquivAffine.symm φ = homMk φ)

end GlobalSections

end AlgebraicGeometry.AlgebraicSpace
