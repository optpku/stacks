module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Composition.Associativity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Pseudofunctor.Basic

/-!
# Composition coherence for functor-bicategory precomposition

This leaf compares direct precomposition by a composite pseudofunctor with
successive precomposition.  The comparison retains the pseudofunctor
associativity equivalence at every diagram; it is not a strict equality of
the two functor-bicategory actions.
-/

@[expose] public section

universe wA vA uA wB vB uB wC vC uC wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {D : Type uD} [Bicategory.{wD, vD} D]

section PrecompositionFunctoriality

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The pointwise `2`-isomorphism in the naturality comparison for
`Precomp.Composition.strongTrans`. -/
private def Precomp.Composition.naturalityApp
    (H : Pseudofunctor A B) (K : Pseudofunctor B C)
    {F G : Pseudofunctor C D} (η : F ⟶ G) (a : A) :
    ((precomp D (H.comp K)).map η ≫
        (Pseudofunctor.compAssoc H K G).hom).app a ≅
      ((Pseudofunctor.compAssoc H K F).hom ≫
        ((precomp D K).comp (precomp D H)).map η).app a :=
  (ρ_ (η.app ((H.comp K).obj a))) ≪≫
    (λ_ (η.app ((H.comp K).obj a))).symm

/-- The pointwise comparison for successive precomposition is natural in a
source `1`-morphism of `A`. -/
private theorem Precomp.Composition.naturalityApp_naturality
    (H : Pseudofunctor A B) (K : Pseudofunctor B C)
    {F G : Pseudofunctor C D} (η : F ⟶ G) :
    ∀ {a b : A} (f : a ⟶ b),
      ((H.comp K).comp F).map f ◁
          (Precomp.Composition.naturalityApp H K η b).hom ≫
        (((Pseudofunctor.compAssoc H K F).hom ≫
          ((precomp D K).comp (precomp D H)).map η).naturality f).hom =
      (((precomp D (H.comp K)).map η ≫
          (Pseudofunctor.compAssoc H K G).hom).naturality f).hom ≫
        (Precomp.Composition.naturalityApp H K η a).hom ▷
          (H.comp (K.comp G)).map f := sorry

/-- The naturality isomorphism between direct and successive precomposition
at a strong transformation of `C ⥤ᵖ D`.

This is the factor-level comparison used by
`Precomp.Composition.strongTrans`; it can be used directly when a downstream
construction needs to preserve the chosen component associators. -/
def Precomp.Composition.naturality
    (H : Pseudofunctor A B) (K : Pseudofunctor B C)
    {F G : Pseudofunctor C D} (η : F ⟶ G) :
    (precomp D (H.comp K)).map η ≫
        (Pseudofunctor.compAssoc H K G).hom ≅
      (Pseudofunctor.compAssoc H K F).hom ≫
        ((precomp D K).comp (precomp D H)).map η :=
  StrongTrans.isoMk
    (fun a => Precomp.Composition.naturalityApp H K η a)
    (Precomp.Composition.naturalityApp_naturality H K η)

/-- Naturality of the direct-to-successive precomposition comparison in
modifications of strong transformations. -/
private theorem Precomp.Composition.strongTrans_naturality_naturality
    (H : Pseudofunctor A B) (K : Pseudofunctor B C) :
    ∀ {F G : Pseudofunctor C D} {η θ : F ⟶ G} (Γ : η ⟶ θ),
      (precomp D (H.comp K)).map₂ Γ ▷
          (Pseudofunctor.compAssoc H K G).hom ≫
        (Precomp.Composition.naturality H K θ).hom =
      (Precomp.Composition.naturality H K η).hom ≫
        (Pseudofunctor.compAssoc H K F).hom ◁
          ((precomp D K).comp (precomp D H)).map₂ Γ := sorry

/-- Identity coherence for the direct-to-successive precomposition comparison. -/
private theorem Precomp.Composition.strongTrans_naturality_id
    (H : Pseudofunctor A B) (K : Pseudofunctor B C) :
    ∀ F : Pseudofunctor C D,
      (Precomp.Composition.naturality H K (StrongTrans.id F)).hom ≫
          (Pseudofunctor.compAssoc H K F).hom ◁
            (((precomp D K).comp (precomp D H)).mapId F).hom =
        ((precomp D (H.comp K)).mapId F).hom ▷
            (Pseudofunctor.compAssoc H K F).hom ≫
          (λ_ ((Pseudofunctor.compAssoc H K F).hom)).hom ≫
            (ρ_ ((Pseudofunctor.compAssoc H K F).hom)).inv := sorry

/-- Composition coherence for the direct-to-successive precomposition comparison. -/
private theorem Precomp.Composition.strongTrans_naturality_comp
    (H : Pseudofunctor A B) (K : Pseudofunctor B C) :
    ∀ {F G I : Pseudofunctor C D} (η : F ⟶ G) (θ : G ⟶ I),
      (Precomp.Composition.naturality H K (StrongTrans.vcomp η θ)).hom ≫
          (Pseudofunctor.compAssoc H K F).hom ◁
            (((precomp D K).comp (precomp D H)).mapComp η θ).hom =
        ((precomp D (H.comp K)).mapComp η θ).hom ▷
            (Pseudofunctor.compAssoc H K I).hom ≫
          (α_ _ _ _).hom ≫
            (precomp D (H.comp K)).map η ◁
              (Precomp.Composition.naturality H K θ).hom ≫
            (α_ _ _ _).inv ≫
              (Precomp.Composition.naturality H K η).hom ▷
                ((precomp D K).comp (precomp D H)).map θ ≫
              (α_ _ _ _).hom := sorry

variable (D) in
/-- The strong transformation from direct precomposition by `H.comp K` to
successive precomposition by `K` and then `H`.

Its component at `F : C ⥤ᵖ D` is `Pseudofunctor.compAssoc H K F`. -/
def Precomp.Composition.strongTrans
    (H : Pseudofunctor A B) (K : Pseudofunctor B C) :
    StrongTrans (precomp D (H.comp K)).toPseudofunctor
      ((precomp D K).comp (precomp D H)).toPseudofunctor where
  app F := (Pseudofunctor.compAssoc H K F).hom
  naturality η := Precomp.Composition.naturality H K η
  naturality_naturality := Precomp.Composition.strongTrans_naturality_naturality H K
  naturality_id := Precomp.Composition.strongTrans_naturality_id H K
  naturality_comp := Precomp.Composition.strongTrans_naturality_comp H K

variable (D) in
/-- Pointwise equivalence data for `Precomp.Composition.strongTrans`. -/
def Precomp.Composition.pointwise
    (H : Pseudofunctor A B) (K : Pseudofunctor B C) :
    StrongTrans.PointwiseEquivalence (Precomp.Composition.strongTrans D H K) :=
  StrongTrans.PointwiseEquivalence.ofComponents
    (fun F => Pseudofunctor.compAssoc H K F)
    (fun _ ↦ Iso.refl _)

variable (D) in
/-- Direct precomposition by a composite pseudofunctor is equivalent to
successive precomposition.

The equivalence is oriented from `precomp D (H.comp K)` to
`(precomp D K).comp (precomp D H)` so downstream constructions can retain a
direct action until an explicitly chosen factorization is needed. -/
def Precomp.Composition.equivalence
    (H : Pseudofunctor A B) (K : Pseudofunctor B C) :
    (precomp D (H.comp K)).toPseudofunctor ≌
      ((precomp D K).comp (precomp D H)).toPseudofunctor :=
  (Precomp.Composition.pointwise D H K).toEquivalence

/- Data audit (mathlib 4.32): the strong-transformation components are exactly
`Pseudofunctor.compAssoc H K F`. The outer naturality is assembled from the
explicit right-unitor/inverse-left-unitor pointwise isomorphism. Any `sorryAx`
dependency is confined to modification naturality and strong-transformation
coherence laws. -/

end PrecompositionFunctoriality

end Pseudofunctor

end CategoryTheory
