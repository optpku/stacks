/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationRestriction
public import Mathlib.CategoryTheory.Sites.GlobalSections

/-! # Restriction along étale isomorphisms

Restriction along an étale isomorphism cancels restriction along its inverse and preserves
global sections of abelian sheaves.
-/

-- Local declaration justification (metaprogramming implementation): exposed concrete maps
-- use private Prop-valued compatibility and naturality laws.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Functor
open Opposite

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The inverse of an étale isomorphism of algebraic spaces is étale. -/
instance instEtale_inv_of_isIso {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] : Etale (inv φ) :=
  sorry

/-- The identity chart maps respect the structure maps after cancelling inverse restriction. -/
private lemma etaleRestriction_comp_inv_w {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ] (U : smallEtaleSite X) :
    (ofOverFunctor S).map (𝟙 U.left) ≫ U.hom = ((etaleRestriction φ ⋙ etaleRestriction (inv φ)).obj U).hom ≫ 𝟙 X :=
  sorry

/-- The identity chart maps identify double restriction with the original chart. -/
private def etaleRestriction_comp_invComponent {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ] (U : smallEtaleSite X) :
    (etaleRestriction φ ⋙ etaleRestriction (inv φ)).obj U ≅ U :=
  MorphismProperty.Comma.isoMk (X := (etaleRestriction φ ⋙ etaleRestriction (inv φ)).obj U) (Y := U) (Iso.refl U.left) (Iso.refl U.right) (etaleRestriction_comp_inv_w φ U)

/-- The cancellation maps commute with morphisms of charts. -/
private lemma etaleRestriction_comp_inv_naturality {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ]
    {U V : smallEtaleSite X} (k : U ⟶ V) :
    (etaleRestriction φ ⋙ etaleRestriction (inv φ)).map k ≫ (etaleRestriction_comp_invComponent φ V).hom =
      (etaleRestriction_comp_invComponent φ U).hom ≫ (𝟭 (smallEtaleSite X)).map k :=
  sorry

/-- Restriction along an étale isomorphism and its inverse cancels on the source site. -/
def etaleRestriction_comp_inv {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ] :
    etaleRestriction φ ⋙ etaleRestriction (inv φ) ≅ 𝟭 (smallEtaleSite X) :=
  NatIso.ofComponents (etaleRestriction_comp_invComponent φ) (fun k => etaleRestriction_comp_inv_naturality φ k)

/-- The identity chart maps respect the structure maps after cancelling inverse restriction. -/
private lemma etaleRestriction_inv_comp_w {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ] (U : smallEtaleSite Y) :
    (ofOverFunctor S).map (𝟙 U.left) ≫ U.hom = ((etaleRestriction (inv φ) ⋙ etaleRestriction φ).obj U).hom ≫ 𝟙 Y :=
  sorry

/-- The identity chart maps identify double restriction with the original chart. -/
private def etaleRestriction_inv_compComponent {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ] (U : smallEtaleSite Y) :
    (etaleRestriction (inv φ) ⋙ etaleRestriction φ).obj U ≅ U :=
  MorphismProperty.Comma.isoMk (X := (etaleRestriction (inv φ) ⋙ etaleRestriction φ).obj U) (Y := U) (Iso.refl U.left) (Iso.refl U.right) (etaleRestriction_inv_comp_w φ U)

/-- The cancellation maps commute with morphisms of charts. -/
private lemma etaleRestriction_inv_comp_naturality {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ]
    {U V : smallEtaleSite Y} (k : U ⟶ V) :
    (etaleRestriction (inv φ) ⋙ etaleRestriction φ).map k ≫ (etaleRestriction_inv_compComponent φ V).hom =
      (etaleRestriction_inv_compComponent φ U).hom ≫ (𝟭 (smallEtaleSite Y)).map k :=
  sorry

/-- Restriction along an étale isomorphism and its inverse cancels on the target site. -/
def etaleRestriction_inv_comp {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ] :
    etaleRestriction (inv φ) ⋙ etaleRestriction φ ≅ 𝟭 (smallEtaleSite Y) :=
  NatIso.ofComponents (etaleRestriction_inv_compComponent φ) (fun k => etaleRestriction_inv_comp_naturality φ k)

/-- The identity chart maps respect the structure maps after cancelling inverse restriction. -/
private lemma spacesEtaleRestriction_comp_inv_w {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ] (U : spacesEtaleSite X) :
    (𝟙 U.left) ≫ U.hom = ((spacesEtaleRestriction φ ⋙ spacesEtaleRestriction (inv φ)).obj U).hom :=
  sorry

/-- The identity chart maps identify double restriction with the original chart. -/
private def spacesEtaleRestriction_comp_invComponent {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ] (U : spacesEtaleSite X) :
    (spacesEtaleRestriction φ ⋙ spacesEtaleRestriction (inv φ)).obj U ≅ U :=
  MorphismProperty.Over.isoMk (A := (spacesEtaleRestriction φ ⋙ spacesEtaleRestriction (inv φ)).obj U) (B := U) (Iso.refl U.left) (spacesEtaleRestriction_comp_inv_w φ U)

/-- The cancellation maps commute with morphisms of charts. -/
private lemma spacesEtaleRestriction_comp_inv_naturality {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ]
    {U V : spacesEtaleSite X} (k : U ⟶ V) :
    (spacesEtaleRestriction φ ⋙ spacesEtaleRestriction (inv φ)).map k ≫ (spacesEtaleRestriction_comp_invComponent φ V).hom =
      (spacesEtaleRestriction_comp_invComponent φ U).hom ≫ (𝟭 (spacesEtaleSite X)).map k :=
  sorry

/-- Restriction along an étale isomorphism and its inverse cancels on the source site. -/
def spacesEtaleRestriction_comp_inv {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ] :
    spacesEtaleRestriction φ ⋙ spacesEtaleRestriction (inv φ) ≅ 𝟭 (spacesEtaleSite X) :=
  NatIso.ofComponents (spacesEtaleRestriction_comp_invComponent φ) (fun k => spacesEtaleRestriction_comp_inv_naturality φ k)

/-- The identity chart maps respect the structure maps after cancelling inverse restriction. -/
private lemma spacesEtaleRestriction_inv_comp_w {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ] (U : spacesEtaleSite Y) :
    (𝟙 U.left) ≫ U.hom = ((spacesEtaleRestriction (inv φ) ⋙ spacesEtaleRestriction φ).obj U).hom :=
  sorry

/-- The identity chart maps identify double restriction with the original chart. -/
private def spacesEtaleRestriction_inv_compComponent {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ] (U : spacesEtaleSite Y) :
    (spacesEtaleRestriction (inv φ) ⋙ spacesEtaleRestriction φ).obj U ≅ U :=
  MorphismProperty.Over.isoMk (A := (spacesEtaleRestriction (inv φ) ⋙ spacesEtaleRestriction φ).obj U) (B := U) (Iso.refl U.left) (spacesEtaleRestriction_inv_comp_w φ U)

/-- The cancellation maps commute with morphisms of charts. -/
private lemma spacesEtaleRestriction_inv_comp_naturality {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ]
    {U V : spacesEtaleSite Y} (k : U ⟶ V) :
    (spacesEtaleRestriction (inv φ) ⋙ spacesEtaleRestriction φ).map k ≫ (spacesEtaleRestriction_inv_compComponent φ V).hom =
      (spacesEtaleRestriction_inv_compComponent φ U).hom ≫ (𝟭 (spacesEtaleSite Y)).map k :=
  sorry

/-- Restriction along an étale isomorphism and its inverse cancels on the target site. -/
def spacesEtaleRestriction_inv_comp {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [IsIso φ] [Etale φ] :
    spacesEtaleRestriction (inv φ) ⋙ spacesEtaleRestriction φ ≅ 𝟭 (spacesEtaleSite Y) :=
  NatIso.ofComponents (spacesEtaleRestriction_inv_compComponent φ) (fun k => spacesEtaleRestriction_inv_comp_naturality φ k)

/-- Double restriction along mutually inverse étale morphisms is continuous. -/
instance etaleRestriction_comp_inv_isContinuous {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] :
    (etaleRestriction φ ⋙ etaleRestriction (inv φ)).IsContinuous
      (smallEtaleTopology X) (smallEtaleTopology X) :=
  Functor.isContinuous_comp (etaleRestriction φ) (etaleRestriction (inv φ))
    (smallEtaleTopology X) (smallEtaleTopology Y) (smallEtaleTopology X)

/-- Double restriction along mutually inverse étale morphisms is continuous. -/
instance etaleRestriction_inv_comp_isContinuous {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] :
    (etaleRestriction (inv φ) ⋙ etaleRestriction φ).IsContinuous
      (smallEtaleTopology Y) (smallEtaleTopology Y) :=
  Functor.isContinuous_comp (etaleRestriction (inv φ)) (etaleRestriction φ)
    (smallEtaleTopology Y) (smallEtaleTopology X) (smallEtaleTopology Y)

/-- Double restriction along mutually inverse étale morphisms is continuous. -/
instance spacesEtaleRestriction_comp_inv_isContinuous {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] :
    (spacesEtaleRestriction φ ⋙ spacesEtaleRestriction (inv φ)).IsContinuous
      (spacesEtaleTopology X) (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (spacesEtaleRestriction φ) (spacesEtaleRestriction (inv φ))
    (spacesEtaleTopology X) (spacesEtaleTopology Y) (spacesEtaleTopology X)

/-- Double restriction along mutually inverse étale morphisms is continuous. -/
instance spacesEtaleRestriction_inv_comp_isContinuous {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] :
    (spacesEtaleRestriction (inv φ) ⋙ spacesEtaleRestriction φ).IsContinuous
      (spacesEtaleTopology Y) (spacesEtaleTopology Y) :=
  Functor.isContinuous_comp (spacesEtaleRestriction (inv φ)) (spacesEtaleRestriction φ)
    (spacesEtaleTopology Y) (spacesEtaleTopology X) (spacesEtaleTopology Y)

/-- Restriction of the global-section cone defines the map on global sections. -/
private def etaleRestrictionSheafGlobalSectionsHom {X Y : AlgebraicSpace S}
    (φ : X ⟶ Y) [Etale φ]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (Sheaf.Γ (smallEtaleTopology Y) AddCommGrpCat.{u + 1}).obj F ⟶
      (Sheaf.Γ (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        ((etaleRestrictionSheaf φ AddCommGrpCat.{u + 1}).obj F) :=
  (((etaleRestrictionSheaf φ AddCommGrpCat.{u + 1}).obj F).isLimitConeΓ).lift
    (F.coneΓ.whisker (etaleRestriction φ).op)

/-- Inverse restriction followed by cancellation recovers global sections on the target. -/
private def etaleRestrictionSheafGlobalSectionsInv {X Y : AlgebraicSpace S}
    (φ : X ⟶ Y) [IsIso φ] [Etale φ]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (Sheaf.Γ (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        ((etaleRestrictionSheaf φ AddCommGrpCat.{u + 1}).obj F) ⟶
      (Sheaf.Γ (smallEtaleTopology Y) AddCommGrpCat.{u + 1}).obj F :=
  etaleRestrictionSheafGlobalSectionsHom (inv φ)
      ((etaleRestrictionSheaf φ AddCommGrpCat.{u + 1}).obj F) ≫
    (Sheaf.Γ (smallEtaleTopology Y) AddCommGrpCat.{u + 1}).map
      ((sheafPushforwardContinuousIso (etaleRestriction_inv_comp φ) AddCommGrpCat.{u + 1}
        (smallEtaleTopology Y) (smallEtaleTopology Y)).hom.app F)

/-- Restriction of global sections is natural in the sheaf. -/
private lemma etaleRestrictionSheafGlobalSectionsIso_naturality {X Y : AlgebraicSpace S}
    (φ : X ⟶ Y) [IsIso φ] [Etale φ]
    {F G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}} (k : F ⟶ G) :
    (Sheaf.Γ (smallEtaleTopology Y) AddCommGrpCat.{u + 1}).map k ≫
        etaleRestrictionSheafGlobalSectionsHom φ G =
      etaleRestrictionSheafGlobalSectionsHom φ F ≫
        (etaleRestrictionSheaf φ AddCommGrpCat.{u + 1} ⋙
          Sheaf.Γ (smallEtaleTopology X) AddCommGrpCat.{u + 1}).map k :=
  sorry

/-- Restricting global sections and then cancelling inverse restriction is the identity. -/
private lemma etaleRestrictionSheafGlobalSectionsIso_hom_inv_id {X Y : AlgebraicSpace S}
    (φ : X ⟶ Y) [IsIso φ] [Etale φ]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    etaleRestrictionSheafGlobalSectionsHom φ F ≫
      etaleRestrictionSheafGlobalSectionsInv φ F = 𝟙 _ :=
  sorry

/-- Cancelling inverse restriction and then restricting global sections is the identity. -/
private lemma etaleRestrictionSheafGlobalSectionsIso_inv_hom_id {X Y : AlgebraicSpace S}
    (φ : X ⟶ Y) [IsIso φ] [Etale φ]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    etaleRestrictionSheafGlobalSectionsInv φ F ≫
      etaleRestrictionSheafGlobalSectionsHom φ F = 𝟙 _ :=
  sorry

/-- Global sections are preserved by restriction along an étale isomorphism. -/
def etaleRestrictionSheafGlobalSectionsIso {X Y : AlgebraicSpace S}
    (φ : X ⟶ Y) [IsIso φ] [Etale φ] :
    Sheaf.Γ (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ≅
      etaleRestrictionSheaf φ AddCommGrpCat.{u + 1} ⋙
        Sheaf.Γ (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents
    (fun F =>
      { hom := etaleRestrictionSheafGlobalSectionsHom φ F
        inv := etaleRestrictionSheafGlobalSectionsInv φ F
        hom_inv_id := etaleRestrictionSheafGlobalSectionsIso_hom_inv_id φ F
        inv_hom_id := etaleRestrictionSheafGlobalSectionsIso_inv_hom_id φ F })
    (fun k => etaleRestrictionSheafGlobalSectionsIso_naturality φ k)

/-- The global-sections identification restricts to the original section on each chart. -/
theorem etaleRestrictionSheafGlobalSectionsIso_hom_ΓRes {X Y : AlgebraicSpace S}
    (φ : X ⟶ Y) [IsIso φ] [Etale φ]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (U : smallEtaleSite X) :
    (etaleRestrictionSheafGlobalSectionsIso φ).hom.app F ≫
        ((etaleRestrictionSheaf φ AddCommGrpCat.{u + 1}).obj F).ΓRes (op U) =
      F.ΓRes (op ((etaleRestriction φ).obj U)) :=
  (((etaleRestrictionSheaf φ AddCommGrpCat.{u + 1}).obj F).isLimitConeΓ).fac
    (F.coneΓ.whisker (etaleRestriction φ).op) (op U)

end AlgebraicGeometry.AlgebraicSpace
