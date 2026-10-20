/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence

/-!
# Associativity coherence for pseudofunctor composition

This leaf supplies the bicategorical equivalence between the two bracketings of
three composable pseudofunctors.  Their object, `1`-morphism, and `2`-morphism
actions agree definitionally, while their pseudofunctor comparison cells need
not; the comparison is therefore a strong-transformation equivalence rather
than an equality of pseudofunctors.
-/

@[expose] public section

universe wB vB uB wC vC uC wD vD uD wE vE uE

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {E : Type uE} [Bicategory.{wE, vE} E]

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The naturality isomorphism of the associativity comparison between the two
bracketings of a composite of three pseudofunctors. -/
private def compAssocStrongTransNaturality
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E)
    {a b : B} (f : a ⟶ b) :
    ((F.comp G).comp H).map f ≫ 𝟙 ((F.comp (G.comp H)).obj b) ≅
      𝟙 (((F.comp G).comp H).obj a) ≫ (F.comp (G.comp H)).map f :=
  (ρ_ (((F.comp G).comp H).map f)) ≪≫
    (λ_ ((F.comp (G.comp H)).map f)).symm

/-- The associativity comparison naturality is compatible with source `2`-cells. -/
private theorem compAssocStrongTrans_naturality_naturality
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E) :
    ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
      ((F.comp G).comp H).map₂ η ▷ 𝟙 ((F.comp (G.comp H)).obj b) ≫
          (compAssocStrongTransNaturality F G H g).hom =
        (compAssocStrongTransNaturality F G H f).hom ≫
          𝟙 (((F.comp G).comp H).obj a) ◁ (F.comp (G.comp H)).map₂ η := sorry

/-- The associativity comparison naturality satisfies the identity coherence equation. -/
private theorem compAssocStrongTrans_naturality_id
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E) :
    ∀ a : B,
      (compAssocStrongTransNaturality F G H (𝟙 a)).hom ≫
          𝟙 (((F.comp G).comp H).obj a) ◁
            ((F.comp (G.comp H)).mapId a).hom =
        (((F.comp G).comp H).mapId a).hom ▷
          𝟙 ((F.comp (G.comp H)).obj a) ≫
            (λ_ (𝟙 ((F.comp (G.comp H)).obj a))).hom ≫
              (ρ_ (𝟙 ((F.comp (G.comp H)).obj a))).inv := sorry

/-- The associativity comparison naturality satisfies the composition coherence equation. -/
private theorem compAssocStrongTrans_naturality_comp
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E) :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      (compAssocStrongTransNaturality F G H (f ≫ g)).hom ≫
          𝟙 (((F.comp G).comp H).obj a) ◁
            ((F.comp (G.comp H)).mapComp f g).hom =
        (((F.comp G).comp H).mapComp f g).hom ▷
          𝟙 ((F.comp (G.comp H)).obj c) ≫
            (α_ _ _ _).hom ≫
              ((F.comp G).comp H).map f ◁
                (compAssocStrongTransNaturality F G H g).hom ≫
                (α_ _ _ _).inv ≫
                  (compAssocStrongTransNaturality F G H f).hom ▷
                    (F.comp (G.comp H)).map g ≫
                    (α_ _ _ _).hom := sorry

namespace compAssoc

/-- The strong transformation underlying the associativity equivalence from the
left-associated composite to the right-associated composite of three pseudofunctors.

Every object component is an identity `1`-morphism. -/
def strongTrans
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E) :
    StrongTrans ((F.comp G).comp H) (F.comp (G.comp H)) where
  app _ := 𝟙 _
  naturality f := compAssocStrongTransNaturality F G H f
  naturality_naturality := compAssocStrongTrans_naturality_naturality F G H
  naturality_id := compAssocStrongTrans_naturality_id F G H
  naturality_comp := compAssocStrongTrans_naturality_comp F G H

/-- Pointwise identity equivalence data for `compAssoc.strongTrans`. -/
def pointwiseEquivalence
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E) :
  StrongTrans.PointwiseEquivalence (strongTrans F G H) :=
  StrongTrans.PointwiseEquivalence.ofComponents
    (fun _ => Bicategory.Equivalence.id _)
    (fun _ ↦ Iso.refl _)

end compAssoc

/-- Associativity equivalence for composition of three pseudofunctors.

This compares the two coherence-bearing pseudofunctor structures without
discarding either bracketing. -/
def compAssoc
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E) :
    (F.comp G).comp H ≌ F.comp (G.comp H) :=
  (compAssoc.pointwiseEquivalence F G H).toEquivalence

end Pseudofunctor

end CategoryTheory
