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
# Postcomposition of strong transformations

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

section Postcomposition

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped Pseudofunctor.StrongTrans

variable {A : Type uA} [Bicategory.{wA, vA} A]

namespace StrongTrans

variable {F G H : Pseudofunctor A B}

/-- The object component obtained by postcomposing a strong transformation with a
pseudofunctor. -/
private def postcompApp
    (η : StrongTrans F G) (K : Pseudofunctor B D) (a : A) :
    (F.comp K).obj a ⟶ (G.comp K).obj a :=
  K.map (η.app a)

/-- The naturality isomorphism obtained by postcomposing a strong transformation with a
pseudofunctor. -/
private def postcompNaturality
    (η : StrongTrans F G) (K : Pseudofunctor B D)
    {a b : A} (f : a ⟶ b) :
    (F.comp K).map f ≫ postcompApp η K b ≅
      postcompApp η K a ≫ (G.comp K).map f :=
  (K.mapComp (F.map f) (η.app b)).symm ≪≫
    K.map₂Iso (η.naturality f) ≪≫
      K.mapComp (η.app a) (G.map f)

/-- Naturality in source `2`-morphisms for postcomposition of a strong transformation. -/
private theorem postcompNaturality_naturality
    (η : StrongTrans F G) (K : Pseudofunctor B D) :
    ∀ {a b : A} {f g : a ⟶ b} (γ : f ⟶ g),
      (F.comp K).map₂ γ ▷ postcompApp η K b ≫
          (postcompNaturality η K g).hom =
        (postcompNaturality η K f).hom ≫
          postcompApp η K a ◁ (G.comp K).map₂ γ := sorry

/-- Identity coherence for postcomposition of a strong transformation. -/
private theorem postcompNaturality_id
    (η : StrongTrans F G) (K : Pseudofunctor B D) :
    ∀ a : A,
      (postcompNaturality η K (𝟙 a)).hom ≫
          postcompApp η K a ◁ ((G.comp K).mapId a).hom =
        ((F.comp K).mapId a).hom ▷ postcompApp η K a ≫
          (λ_ (postcompApp η K a)).hom ≫
          (ρ_ (postcompApp η K a)).inv := sorry

/-- Composition coherence for postcomposition of a strong transformation. -/
private theorem postcompNaturality_comp
    (η : StrongTrans F G) (K : Pseudofunctor B D) :
    ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c),
      (postcompNaturality η K (f ≫ g)).hom ≫
          postcompApp η K a ◁ ((G.comp K).mapComp f g).hom =
        ((F.comp K).mapComp f g).hom ▷ postcompApp η K c ≫
          (α_ _ _ _).hom ≫
          (F.comp K).map f ◁ (postcompNaturality η K g).hom ≫
          (α_ _ _ _).inv ≫
          (postcompNaturality η K f).hom ▷ (G.comp K).map g ≫
          (α_ _ _ _).hom := sorry

/-- Postcompose a strong transformation by a pseudofunctor. Its components are obtained by
applying the fixed pseudofunctor, while its naturality includes the two composition
comparisons of that pseudofunctor. -/
def postcomp (η : StrongTrans F G) (K : Pseudofunctor B D) :
    StrongTrans (F.comp K) (G.comp K) where
  app := postcompApp η K
  naturality := postcompNaturality η K
  naturality_naturality := postcompNaturality_naturality η K
  naturality_id := postcompNaturality_id η K
  naturality_comp := postcompNaturality_comp η K

/-- Components of a postcomposed strong transformation are mapped components of the original
transformation. -/
@[simp]
theorem postcomp.app
    (η : StrongTrans F G) (K : Pseudofunctor B D) (a : A) :
    (η.postcomp K).app a = K.map (η.app a) := sorry

/-- Naturality of a postcomposed strong transformation is the image of the original
naturality, conjugated by the composition comparisons of the fixed pseudofunctor. -/
@[simp]
theorem postcomp.naturality
    (η : StrongTrans F G) (K : Pseudofunctor B D)
    {a b : A} (f : a ⟶ b) :
    (η.postcomp K).naturality f =
      (K.mapComp (F.map f) (η.app b)).symm ≪≫
        K.map₂Iso (η.naturality f) ≪≫
          K.mapComp (η.app a) (G.map f) := sorry

end StrongTrans

end Postcomposition

end Pseudofunctor

end CategoryTheory
