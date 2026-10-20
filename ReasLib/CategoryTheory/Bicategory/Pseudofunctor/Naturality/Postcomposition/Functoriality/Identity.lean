/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Composition
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Pseudofunctor.Basic

/-!
# Identity coherence for functor-bicategory postcomposition

This leaf compares postcomposition by an identity pseudofunctor with the
identity action on a pseudofunctor bicategory. Its comparison retains the
right-unit equivalence of every diagram rather than identifying the two
coherence-bearing actions strictly.
-/

@[expose] public section

universe wA vA uA wB vB uB

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]

section PostcompositionFunctoriality

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The pointwise `2`-isomorphism in the naturality comparison for
`Postcomp.Identity.strongTrans`. -/
private def Postcomp.Identity.naturalityApp
    {F G : Pseudofunctor A B} (η : F ⟶ G) (a : A) :
    ((postcomp A (Pseudofunctor.id B)).map η ≫
        (Pseudofunctor.compId G).hom).app a ≅
      ((Pseudofunctor.compId F).hom ≫
        (Pseudofunctor.id (Pseudofunctor A B)).map η).app a :=
  (ρ_ (η.app a)) ≪≫ (λ_ (η.app a)).symm

/-- The pointwise comparison for identity postcomposition is natural in a
source `1`-morphism of `A`. -/
private theorem Postcomp.Identity.naturalityApp_naturality
    {F G : Pseudofunctor A B} (η : F ⟶ G) :
    ∀ {a b : A} (f : a ⟶ b),
      (F.comp (Pseudofunctor.id B)).map f ◁
          (Postcomp.Identity.naturalityApp η b).hom ≫
        (((Pseudofunctor.compId F).hom ≫
          (Pseudofunctor.id (Pseudofunctor A B)).map η).naturality f).hom =
      (((postcomp A (Pseudofunctor.id B)).map η ≫
          (Pseudofunctor.compId G).hom).naturality f).hom ≫
        (Postcomp.Identity.naturalityApp η a).hom ▷ G.map f := sorry

/-- The naturality isomorphism between identity postcomposition and the identity
action at a strong transformation of `A ⥤ᵖ B`.

This factor-level comparison is used by `Postcomp.Identity.strongTrans` and is
available directly when a downstream construction must retain the chosen
diagram right-unit components. -/
def Postcomp.Identity.naturality
    {F G : Pseudofunctor A B} (η : F ⟶ G) :
    (postcomp A (Pseudofunctor.id B)).map η ≫
        (Pseudofunctor.compId G).hom ≅
      (Pseudofunctor.compId F).hom ≫
        (Pseudofunctor.id (Pseudofunctor A B)).map η :=
  StrongTrans.isoMk
    (fun a => Postcomp.Identity.naturalityApp η a)
    (Postcomp.Identity.naturalityApp_naturality η)

/-- Naturality of the identity-postcomposition comparison in modifications of
strong transformations. -/
private theorem Postcomp.Identity.strongTrans_naturality_naturality :
    ∀ {F G : Pseudofunctor A B} {η θ : F ⟶ G} (Γ : η ⟶ θ),
      (postcomp A (Pseudofunctor.id B)).map₂ Γ ▷
          (Pseudofunctor.compId G).hom ≫
        (Postcomp.Identity.naturality θ).hom =
      (Postcomp.Identity.naturality η).hom ≫
        (Pseudofunctor.compId F).hom ◁
          (Pseudofunctor.id (Pseudofunctor A B)).map₂ Γ := sorry

/-- Identity coherence for the identity-postcomposition comparison. -/
private theorem Postcomp.Identity.strongTrans_naturality_id :
    ∀ F : Pseudofunctor A B,
      (Postcomp.Identity.naturality (StrongTrans.id F)).hom ≫
          (Pseudofunctor.compId F).hom ◁
            ((Pseudofunctor.id (Pseudofunctor A B)).mapId F).hom =
        ((postcomp A (Pseudofunctor.id B)).mapId F).hom ▷
            (Pseudofunctor.compId F).hom ≫
          (λ_ ((Pseudofunctor.compId F).hom)).hom ≫
            (ρ_ ((Pseudofunctor.compId F).hom)).inv := sorry

/-- Composition coherence for the identity-postcomposition comparison. -/
private theorem Postcomp.Identity.strongTrans_naturality_comp :
    ∀ {F G I : Pseudofunctor A B} (η : F ⟶ G) (θ : G ⟶ I),
      (Postcomp.Identity.naturality (StrongTrans.vcomp η θ)).hom ≫
          (Pseudofunctor.compId F).hom ◁
            ((Pseudofunctor.id (Pseudofunctor A B)).mapComp η θ).hom =
        ((postcomp A (Pseudofunctor.id B)).mapComp η θ).hom ▷
            (Pseudofunctor.compId I).hom ≫
          (α_ _ _ _).hom ≫
            (postcomp A (Pseudofunctor.id B)).map η ◁
              (Postcomp.Identity.naturality θ).hom ≫
            (α_ _ _ _).inv ≫
              (Postcomp.Identity.naturality η).hom ▷
                (Pseudofunctor.id (Pseudofunctor A B)).map θ ≫
              (α_ _ _ _).hom := sorry

variable (A) (B) in
/-- The strong transformation from postcomposition by the identity
pseudofunctor to the identity action on `A ⥤ᵖ B`.

Its component at `F : A ⥤ᵖ B` is `Pseudofunctor.compId F`. -/
def Postcomp.Identity.strongTrans :
    StrongTrans (postcomp A (Pseudofunctor.id B))
      (Pseudofunctor.id (Pseudofunctor A B)) where
  app F := (Pseudofunctor.compId F).hom
  naturality η := Postcomp.Identity.naturality η
  naturality_naturality := Postcomp.Identity.strongTrans_naturality_naturality
  naturality_id := Postcomp.Identity.strongTrans_naturality_id
  naturality_comp := Postcomp.Identity.strongTrans_naturality_comp

variable (A) (B) in
/-- Pointwise equivalence data for `Postcomp.Identity.strongTrans`. -/
def Postcomp.Identity.pointwise :
    StrongTrans.PointwiseEquivalence (Postcomp.Identity.strongTrans A B) :=
  StrongTrans.PointwiseEquivalence.ofComponents
    (fun F => Pseudofunctor.compId F)
    (fun _ ↦ Iso.refl _)

variable (A) (B) in
/-- Postcomposition by an identity pseudofunctor is equivalent to the identity
action on the corresponding pseudofunctor bicategory.

The equivalence is oriented from `postcomp A (Pseudofunctor.id B)` to the
identity action so downstream constructions can preserve the explicit
postcomposition action until a unit comparison is chosen. -/
def Postcomp.Identity.equivalence :
    postcomp A (Pseudofunctor.id B) ≌ Pseudofunctor.id (Pseudofunctor A B) :=
  (Postcomp.Identity.pointwise A B).toEquivalence

/- Data audit (mathlib 4.32): the strong-transformation components are exactly
the forward morphisms of `Pseudofunctor.compId F`. The outer naturality is
assembled from the explicit right-unitor/inverse-left-unitor pointwise
isomorphism. Any `sorryAx` dependency is confined to modification naturality
and strong-transformation coherence laws. -/

end PostcompositionFunctoriality

end Pseudofunctor

end CategoryTheory
