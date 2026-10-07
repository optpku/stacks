module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Composition.Identity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Pseudofunctor.Basic

/-!
# Identity coherence for functor-bicategory precomposition

This leaf compares precomposition by the identity pseudofunctor with the
identity action on a pseudofunctor bicategory.  Its components retain the
ordinary pseudofunctor left-unit equivalences rather than suppressing their
comparison cells by a strict equality.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]

section PrecompositionFunctoriality

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The pointwise `2`-isomorphism in the naturality comparison for
`Precomp.Identity.strongTrans`. -/
private def Precomp.Identity.naturalityApp
    {F G : Pseudofunctor B D} (η : F ⟶ G) (b : B) :
    ((precomp D (Pseudofunctor.id B)).map η ≫
        (Pseudofunctor.idComp G).hom).app b ≅
      ((Pseudofunctor.idComp F).hom ≫
        (Pseudofunctor.id (Pseudofunctor B D)).map η).app b :=
  (ρ_ (η.app b)) ≪≫ (λ_ (η.app b)).symm

/-- The pointwise identity-action comparison is natural in a source
`1`-morphism of `B`. -/
private theorem Precomp.Identity.naturalityApp_naturality
    {F G : Pseudofunctor B D} (η : F ⟶ G) :
    ∀ {a b : B} (f : a ⟶ b),
      ((Pseudofunctor.id B).comp F).map f ◁
          (Precomp.Identity.naturalityApp η b).hom ≫
        (((Pseudofunctor.idComp F).hom ≫
          (Pseudofunctor.id (Pseudofunctor B D)).map η).naturality f).hom =
      (((precomp D (Pseudofunctor.id B)).map η ≫
          (Pseudofunctor.idComp G).hom).naturality f).hom ≫
        (Precomp.Identity.naturalityApp η a).hom ▷ G.map f := sorry

/-- The naturality isomorphism between precomposition by the identity and the
identity functor-bicategory action.

This is the factor-level comparison used by
`Precomp.Identity.strongTrans`. -/
def Precomp.Identity.naturality
    {F G : Pseudofunctor B D} (η : F ⟶ G) :
    (precomp D (Pseudofunctor.id B)).map η ≫
        (Pseudofunctor.idComp G).hom ≅
      (Pseudofunctor.idComp F).hom ≫
        (Pseudofunctor.id (Pseudofunctor B D)).map η :=
  StrongTrans.isoMk
    (fun b => Precomp.Identity.naturalityApp η b)
    (Precomp.Identity.naturalityApp_naturality η)

/-- Naturality of the identity-action comparison in modifications of strong
transformations. -/
private theorem Precomp.Identity.strongTrans_naturality_naturality :
    ∀ {F G : Pseudofunctor B D} {η θ : F ⟶ G} (Γ : η ⟶ θ),
      (precomp D (Pseudofunctor.id B)).map₂ Γ ▷
          (Pseudofunctor.idComp G).hom ≫
        (Precomp.Identity.naturality θ).hom =
      (Precomp.Identity.naturality η).hom ≫
        (Pseudofunctor.idComp F).hom ◁
          (Pseudofunctor.id (Pseudofunctor B D)).map₂ Γ := sorry

/-- Identity coherence for the precomposition-identity comparison. -/
private theorem Precomp.Identity.strongTrans_naturality_id :
    ∀ F : Pseudofunctor B D,
      (Precomp.Identity.naturality (StrongTrans.id F)).hom ≫
          (Pseudofunctor.idComp F).hom ◁
            ((Pseudofunctor.id (Pseudofunctor B D)).mapId F).hom =
        ((precomp D (Pseudofunctor.id B)).mapId F).hom ▷
            (Pseudofunctor.idComp F).hom ≫
          (λ_ ((Pseudofunctor.idComp F).hom)).hom ≫
            (ρ_ ((Pseudofunctor.idComp F).hom)).inv := sorry

/-- Composition coherence for the precomposition-identity comparison. -/
private theorem Precomp.Identity.strongTrans_naturality_comp :
    ∀ {F G I : Pseudofunctor B D} (η : F ⟶ G) (θ : G ⟶ I),
      (Precomp.Identity.naturality (StrongTrans.vcomp η θ)).hom ≫
          (Pseudofunctor.idComp F).hom ◁
            ((Pseudofunctor.id (Pseudofunctor B D)).mapComp η θ).hom =
        ((precomp D (Pseudofunctor.id B)).mapComp η θ).hom ▷
            (Pseudofunctor.idComp I).hom ≫
          (α_ _ _ _).hom ≫
            (precomp D (Pseudofunctor.id B)).map η ◁
              (Precomp.Identity.naturality θ).hom ≫
            (α_ _ _ _).inv ≫
              (Precomp.Identity.naturality η).hom ▷
                (Pseudofunctor.id (Pseudofunctor B D)).map θ ≫
              (α_ _ _ _).hom := sorry

variable (B) (D) in
/-- The strong transformation from precomposition by `Pseudofunctor.id B` to
the identity pseudofunctor of `Pseudofunctor B D`.

Its component at `F` is `Pseudofunctor.idComp F`. -/
def Precomp.Identity.strongTrans :
    StrongTrans (precomp D (Pseudofunctor.id B)).toPseudofunctor
      (Pseudofunctor.id (Pseudofunctor B D)) where
  app F := (Pseudofunctor.idComp F).hom
  naturality η := Precomp.Identity.naturality η
  naturality_naturality := Precomp.Identity.strongTrans_naturality_naturality
  naturality_id := Precomp.Identity.strongTrans_naturality_id
  naturality_comp := Precomp.Identity.strongTrans_naturality_comp

variable (B) (D) in
/-- Pointwise equivalence data for `Precomp.Identity.strongTrans`. -/
def Precomp.Identity.pointwise :
    StrongTrans.PointwiseEquivalence (Precomp.Identity.strongTrans B D) :=
  StrongTrans.PointwiseEquivalence.ofComponents
    (fun F => Pseudofunctor.idComp F)
    (fun _ ↦ Iso.refl _)

variable (B) (D) in
/-- Precomposition by the identity pseudofunctor is equivalent to the identity
action on `Pseudofunctor B D`. -/
def Precomp.Identity.equivalence :
    (precomp D (Pseudofunctor.id B)).toPseudofunctor ≌
      Pseudofunctor.id (Pseudofunctor B D) :=
    (Precomp.Identity.pointwise B D).toEquivalence

/- Data audit (mathlib 4.32): every object component is exactly
`Pseudofunctor.idComp F`. The outer naturality is assembled from the explicit
right-unitor/inverse-left-unitor pointwise isomorphism. Any `sorryAx`
dependency is confined to modification naturality and strong-transformation
coherence laws. -/

end PrecompositionFunctoriality

end Pseudofunctor

end CategoryTheory
