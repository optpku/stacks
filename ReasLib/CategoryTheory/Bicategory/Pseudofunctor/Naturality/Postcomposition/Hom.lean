module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Modification

/-!
# Hom-category postcomposition in pseudofunctor bicategories

The action of a fixed pseudofunctor on functor-bicategory `2`-morphisms and
the induced functor between strong-transformation hom-categories.
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

namespace Hom

variable {η θ ι : StrongTrans F G}

/-- Postcompose a `2`-morphism in the functor bicategory by a pseudofunctor. -/
def postcomp (Γ : Hom η θ) (K : Pseudofunctor B D) :
    Hom (η.postcomp K) (θ.postcomp K) :=
  ⟨Γ.as.postcomp K⟩

/-- The underlying modification of a postcomposed functor-bicategory `2`-morphism. -/
@[simp]
theorem postcomp.as
    (Γ : Hom η θ) (K : Pseudofunctor B D) :
    (Γ.postcomp K).as = Γ.as.postcomp K := sorry

/-- Components of a postcomposed functor-bicategory `2`-morphism. -/
@[simp]
theorem postcomp.app
    (Γ : Hom η θ) (K : Pseudofunctor B D) (a : A) :
    (Γ.postcomp K).as.app a = K.map₂ (Γ.as.app a) := sorry

end Hom

/-- Postcomposition preserves identity `2`-morphisms in the functor bicategory. -/
@[simp]
theorem postcomp₂.id
    (η : StrongTrans F G) (K : Pseudofunctor B D) :
    StrongTrans.Hom.postcomp
        (Hom.of (Modification.id η)) K =
      Hom.of (Modification.id (η.postcomp K)) := sorry

/-- Postcomposition preserves vertical composition in the functor bicategory. -/
@[simp]
theorem postcomp₂.comp
    {η θ ι : StrongTrans F G}
    (Γ : Hom η θ) (Δ : Hom θ ι) (K : Pseudofunctor B D) :
    StrongTrans.Hom.postcomp
        (Hom.of (Modification.vcomp Γ.as Δ.as)) K =
      Hom.of
        (Modification.vcomp (Γ.as.postcomp K) (Δ.as.postcomp K)) := sorry

end StrongTrans

/-- Postcomposition on a hom-category of the pseudofunctor bicategory. -/
def postcompHom
    (K : Pseudofunctor B D) (F G : Pseudofunctor A B) :
    (F ⟶ G) ⥤ (F.comp K ⟶ G.comp K) where
  obj η := η.postcomp K
  map Γ := StrongTrans.Hom.postcomp Γ K
  map_id η := StrongTrans.postcomp₂.id η K
  map_comp Γ Δ := StrongTrans.postcomp₂.comp Γ Δ K

/-- The object action of `postcompHom` is postcomposition of strong transformations. -/
@[simp]
theorem postcompHom.obj
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    (η : F ⟶ G) :
    (postcompHom K F G).obj η = η.postcomp K := sorry

/-- The morphism action of `postcompHom` is postcomposition of modifications. -/
@[simp]
theorem postcompHom.map
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) :
    (postcompHom K F G).map Γ =
      StrongTrans.Hom.postcomp Γ K := sorry

end Postcomposition

end Pseudofunctor

end CategoryTheory
