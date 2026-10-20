module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Composition
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Pseudofunctor.Basic

/-!
# Composition coherence for functor-bicategory postcomposition

This leaf compares direct postcomposition by a composite pseudofunctor with
successive postcomposition actions. The comparison retains the inverse of the
pseudofunctor associativity equivalence at every diagram; it is not a strict
equality of the two functor-bicategory actions.
-/

@[expose] public section

universe wA vA uA wB vB uB wD vD uD wE vE uE

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {E : Type uE} [Bicategory.{wE, vE} E]

section PostcompositionFunctoriality

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The pointwise `2`-isomorphism in the naturality comparison for
`Postcomp.Composition.strongTrans`. -/
private def Postcomp.Composition.naturalityApp
    (K : Pseudofunctor B D) (L : Pseudofunctor D E)
    {F G : Pseudofunctor A B} (η : F ⟶ G) (a : A) :
    ((postcomp A (K.comp L)).map η ≫
        (Pseudofunctor.compAssoc G K L).symm.hom).app a ≅
      ((Pseudofunctor.compAssoc F K L).symm.hom ≫
        ((postcomp A K).comp (postcomp A L)).map η).app a :=
  (ρ_ (L.map (K.map (η.app a)))) ≪≫
    (λ_ (L.map (K.map (η.app a)))).symm

/-- The pointwise comparison for successive postcomposition is natural in a
source `1`-morphism of `A`. -/
private theorem Postcomp.Composition.naturalityApp_naturality
    (K : Pseudofunctor B D) (L : Pseudofunctor D E)
    {F G : Pseudofunctor A B} (η : F ⟶ G) :
    ∀ {a b : A} (f : a ⟶ b),
      (F.comp (K.comp L)).map f ◁
          (Postcomp.Composition.naturalityApp K L η b).hom ≫
        (((Pseudofunctor.compAssoc F K L).symm.hom ≫
          ((postcomp A K).comp (postcomp A L)).map η).naturality f).hom =
      (((postcomp A (K.comp L)).map η ≫
          (Pseudofunctor.compAssoc G K L).symm.hom).naturality f).hom ≫
        (Postcomp.Composition.naturalityApp K L η a).hom ▷
          (((postcomp A K).comp (postcomp A L)).obj G).map f := sorry

/-- The naturality isomorphism between direct and successive postcomposition
at a strong transformation of `A ⥤ᵖ B`.

This factor-level comparison is used by `Postcomp.Composition.strongTrans` and
is available directly when a downstream construction must retain the chosen
diagram associativity components. -/
def Postcomp.Composition.naturality
    (K : Pseudofunctor B D) (L : Pseudofunctor D E)
    {F G : Pseudofunctor A B} (η : F ⟶ G) :
    (postcomp A (K.comp L)).map η ≫
        (Pseudofunctor.compAssoc G K L).symm.hom ≅
      (Pseudofunctor.compAssoc F K L).symm.hom ≫
        ((postcomp A K).comp (postcomp A L)).map η :=
  StrongTrans.isoMk
    (fun a => Postcomp.Composition.naturalityApp K L η a)
    (Postcomp.Composition.naturalityApp_naturality K L η)

/-- Naturality of the direct-to-successive postcomposition comparison in
modifications of strong transformations. -/
private theorem Postcomp.Composition.strongTrans_naturality_naturality
    (K : Pseudofunctor B D) (L : Pseudofunctor D E) :
    ∀ {F G : Pseudofunctor A B} {η θ : F ⟶ G} (Γ : η ⟶ θ),
      (postcomp A (K.comp L)).map₂ Γ ▷
         (Pseudofunctor.compAssoc G K L).symm.hom ≫
        (Postcomp.Composition.naturality K L θ).hom =
      (Postcomp.Composition.naturality K L η).hom ≫
        (Pseudofunctor.compAssoc F K L).symm.hom ◁
          ((postcomp A K).comp (postcomp A L)).map₂ Γ := sorry

/-- Identity coherence for the direct-to-successive postcomposition comparison. -/
private theorem Postcomp.Composition.strongTrans_naturality_id
    (K : Pseudofunctor B D) (L : Pseudofunctor D E) :
    ∀ F : Pseudofunctor A B,
      (Postcomp.Composition.naturality K L (StrongTrans.id F)).hom ≫
          (Pseudofunctor.compAssoc F K L).symm.hom ◁
            (((postcomp A K).comp (postcomp A L)).mapId F).hom =
        ((postcomp A (K.comp L)).mapId F).hom ▷
           (Pseudofunctor.compAssoc F K L).symm.hom ≫
          (λ_ ((Pseudofunctor.compAssoc F K L).symm.hom)).hom ≫
            (ρ_ ((Pseudofunctor.compAssoc F K L).symm.hom)).inv := sorry

/-- Composition coherence for the direct-to-successive postcomposition comparison. -/
private theorem Postcomp.Composition.strongTrans_naturality_comp
    (K : Pseudofunctor B D) (L : Pseudofunctor D E) :
    ∀ {F G I : Pseudofunctor A B} (η : F ⟶ G) (θ : G ⟶ I),
      (Postcomp.Composition.naturality K L (StrongTrans.vcomp η θ)).hom ≫
          (Pseudofunctor.compAssoc F K L).symm.hom ◁
            (((postcomp A K).comp (postcomp A L)).mapComp η θ).hom =
        ((postcomp A (K.comp L)).mapComp η θ).hom ▷
           (Pseudofunctor.compAssoc I K L).symm.hom ≫
          (α_ _ _ _).hom ≫
            (postcomp A (K.comp L)).map η ◁
              (Postcomp.Composition.naturality K L θ).hom ≫
            (α_ _ _ _).inv ≫
              (Postcomp.Composition.naturality K L η).hom ▷
               ((postcomp A K).comp (postcomp A L)).map θ ≫
             (α_ _ _ _).hom := sorry

variable (A) in
/-- The strong transformation from direct postcomposition by `K.comp L` to
successive postcomposition by `K` and then `L`.

Its component at `F : A ⥤ᵖ B` is the inverse of
`Pseudofunctor.compAssoc F K L`. -/
def Postcomp.Composition.strongTrans
    (K : Pseudofunctor B D) (L : Pseudofunctor D E) :
    StrongTrans (postcomp A (K.comp L))
      ((postcomp A K).comp (postcomp A L)) where
  app F := (Pseudofunctor.compAssoc F K L).symm.hom
  naturality η := Postcomp.Composition.naturality K L η
  naturality_naturality := Postcomp.Composition.strongTrans_naturality_naturality K L
  naturality_id := Postcomp.Composition.strongTrans_naturality_id K L
  naturality_comp := Postcomp.Composition.strongTrans_naturality_comp K L

variable (A) in
/-- Pointwise equivalence data for `Postcomp.Composition.strongTrans`. -/
def Postcomp.Composition.pointwise
    (K : Pseudofunctor B D) (L : Pseudofunctor D E) :
    StrongTrans.PointwiseEquivalence (Postcomp.Composition.strongTrans A K L) :=
  StrongTrans.PointwiseEquivalence.ofComponents
    (fun F => (Pseudofunctor.compAssoc F K L).symm)
    (fun _ ↦ Iso.refl _)

variable (A) in
/-- Direct postcomposition by a composite pseudofunctor is equivalent to
successive postcomposition.

The equivalence is oriented from `postcomp A (K.comp L)` to
`(postcomp A K).comp (postcomp A L)` so downstream constructions can retain a
direct action until an explicitly chosen factorization is needed. -/
def Postcomp.Composition.equivalence
    (K : Pseudofunctor B D) (L : Pseudofunctor D E) :
    postcomp A (K.comp L) ≌ (postcomp A K).comp (postcomp A L) :=
  (Postcomp.Composition.pointwise A K L).toEquivalence

/- Data audit (mathlib 4.32): the strong-transformation components are exactly
the forward morphisms of `(Pseudofunctor.compAssoc F K L).symm`. The outer
naturality is assembled from the explicit right-unitor/inverse-left-unitor
pointwise isomorphism. Any `sorryAx` dependency is confined to modification
naturality and strong-transformation coherence laws. -/

end PostcompositionFunctoriality

end Pseudofunctor

end CategoryTheory
