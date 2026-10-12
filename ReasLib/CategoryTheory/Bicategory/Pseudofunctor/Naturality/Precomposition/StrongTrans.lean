/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Precomposition of strong transformations

The pointwise action of a fixed pseudofunctor on strong transformations in a
pseudofunctor bicategory. Modification and hom-category actions live in their
own leaf modules.
-/

@[expose] public section

universe wA vA uA wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

section Precomposition

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped Pseudofunctor.StrongTrans

variable {A : Type uA} [Bicategory.{wA, vA} A]

namespace StrongTrans

variable {F G H : Pseudofunctor B D}

/-- Naturality in source `2`-morphisms for precomposition of a strong transformation. -/
private theorem precomp_naturality_naturality
    (η : StrongTrans F G) (K : Pseudofunctor A B) :
    ∀ {a b : A} {f g : a ⟶ b} (γ : f ⟶ g),
      (K.comp F).map₂ γ ▷ η.app (K.obj b) ≫
          (η.naturality (K.map g)).hom =
        (η.naturality (K.map f)).hom ≫
          η.app (K.obj a) ◁ (K.comp G).map₂ γ := sorry

/-- Identity coherence for precomposition of a strong transformation. -/
private theorem precomp_naturality_id
    (η : StrongTrans F G) (K : Pseudofunctor A B) :
    ∀ a : A,
      (η.naturality (K.map (𝟙 a))).hom ≫
          η.app (K.obj a) ◁ ((K.comp G).mapId a).hom =
        ((K.comp F).mapId a).hom ▷ η.app (K.obj a) ≫
          (λ_ (η.app (K.obj a))).hom ≫
          (ρ_ (η.app (K.obj a))).inv := sorry

/-- Composition coherence for precomposition of a strong transformation. -/
private theorem precomp_naturality_comp
    (η : StrongTrans F G) (K : Pseudofunctor A B) :
    ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c),
      (η.naturality (K.map (f ≫ g))).hom ≫
          η.app (K.obj a) ◁ ((K.comp G).mapComp f g).hom =
        ((K.comp F).mapComp f g).hom ▷ η.app (K.obj c) ≫
          (α_ _ _ _).hom ≫
          (K.comp F).map f ◁ (η.naturality (K.map g)).hom ≫
          (α_ _ _ _).inv ≫
          (η.naturality (K.map f)).hom ▷ (K.comp G).map g ≫
          (α_ _ _ _).hom := sorry

/-- Precompose a strong transformation by a pseudofunctor. Components and naturality are
obtained by evaluating the original transformation on the object and `1`-morphism images
of the precomposing pseudofunctor. -/
def precomp (η : StrongTrans F G) (K : Pseudofunctor A B) :
    StrongTrans (K.comp F) (K.comp G) where
  app a := η.app (K.obj a)
  naturality f := η.naturality (K.map f)
  naturality_naturality := precomp_naturality_naturality η K
  naturality_id := precomp_naturality_id η K
  naturality_comp := precomp_naturality_comp η K

/-- Components of a precomposed strong transformation are evaluated at the image object. -/
@[simp]
theorem precomp.app
    (η : StrongTrans F G) (K : Pseudofunctor A B) (a : A) :
    (η.precomp K).app a = η.app (K.obj a) := sorry

/-- Naturality of a precomposed strong transformation is evaluated at the image
`1`-morphism. -/
@[simp]
theorem precomp.naturality
    (η : StrongTrans F G) (K : Pseudofunctor A B)
    {a b : A} (f : a ⟶ b) :
    (η.precomp K).naturality f = η.naturality (K.map f) := sorry

/-- Precomposition preserves identity strong transformations. -/
@[simp]
theorem precomp.id
    (F : Pseudofunctor B D) (K : Pseudofunctor A B) :
    (StrongTrans.id F).precomp K =
      StrongTrans.id (K.comp F) := sorry

/-- Precomposition preserves vertical composition of strong transformations. -/
@[simp]
theorem precomp.vcomp
    {F G H : Pseudofunctor B D} (η : StrongTrans F G)
    (θ : StrongTrans G H) (K : Pseudofunctor A B) :
    (StrongTrans.vcomp η θ).precomp K =
      StrongTrans.vcomp (η.precomp K) (θ.precomp K) := sorry

end StrongTrans

end Precomposition

end Pseudofunctor

end CategoryTheory
