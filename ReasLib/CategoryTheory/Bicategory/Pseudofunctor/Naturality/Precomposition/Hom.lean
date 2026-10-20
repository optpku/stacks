/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Modification

/-!
# Hom-category precomposition in pseudofunctor bicategories

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

section Precomposition

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped Pseudofunctor.StrongTrans

variable {A : Type uA} [Bicategory.{wA, vA} A]

namespace StrongTrans

variable {F G H : Pseudofunctor B D}

namespace Hom

variable {η θ ι : StrongTrans F G}

/-- Precompose a `2`-morphism in the functor bicategory by a pseudofunctor. -/
def precomp (Γ : Hom η θ) (K : Pseudofunctor A B) :
    Hom (η.precomp K) (θ.precomp K) :=
  ⟨Γ.as.precomp K⟩

/-- The underlying modification of a precomposed functor-bicategory `2`-morphism. -/
@[simp]
theorem precomp.as
    (Γ : Hom η θ) (K : Pseudofunctor A B) :
    (Γ.precomp K).as = Γ.as.precomp K := sorry

/-- Components of a precomposed functor-bicategory `2`-morphism. -/
@[simp]
theorem precomp.app
    (Γ : Hom η θ) (K : Pseudofunctor A B) (a : A) :
    (Γ.precomp K).as.app a = Γ.as.app (K.obj a) := sorry

end Hom

/-- Precomposition preserves identity `2`-morphisms in the functor bicategory. -/
@[simp]
theorem precomp₂.id
    (η : StrongTrans F G) (K : Pseudofunctor A B) :
    StrongTrans.Hom.precomp
        (Hom.of (Modification.id η)) K =
      Hom.of (Modification.id (η.precomp K)) := sorry

/-- Precomposition preserves vertical composition in the functor bicategory. -/
@[simp]
theorem precomp₂.comp
    {η θ ι : StrongTrans F G}
    (Γ : Hom η θ) (Δ : Hom θ ι) (K : Pseudofunctor A B) :
    StrongTrans.Hom.precomp
        (Hom.of (Modification.vcomp Γ.as Δ.as)) K =
      Hom.of
        (Modification.vcomp (Γ.as.precomp K) (Δ.as.precomp K)) := sorry

end StrongTrans

/-- Precomposition on a hom-category of the pseudofunctor bicategory. -/
def precompHom
    (K : Pseudofunctor A B) (F G : Pseudofunctor B D) :
    (F ⟶ G) ⥤ (K.comp F ⟶ K.comp G) where
  obj η := η.precomp K
  map Γ := StrongTrans.Hom.precomp Γ K
  map_id η := StrongTrans.precomp₂.id η K
  map_comp Γ Δ := StrongTrans.precomp₂.comp Γ Δ K

/-- The object action of `precompHom` is precomposition of strong transformations. -/
@[simp]
theorem precompHom.obj
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    (η : F ⟶ G) :
    (precompHom K F G).obj η = η.precomp K := sorry

/-- The morphism action of `precompHom` is precomposition of modifications. -/
@[simp]
theorem precompHom.map
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) :
    (precompHom K F G).map Γ =
      StrongTrans.Hom.precomp Γ K := sorry

end Precomposition

end Pseudofunctor

end CategoryTheory
