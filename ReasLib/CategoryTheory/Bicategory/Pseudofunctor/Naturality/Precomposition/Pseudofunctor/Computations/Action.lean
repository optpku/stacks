module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Pseudofunctor.Basic

/-!
# Action computations for pseudofunctorial precomposition

Object, `1`-morphism, and `2`-morphism formulas for the precomposition
pseudofunctor and the pseudofunctors it produces.
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

/-- The object action of functor-bicategory precomposition is composition with the fixed
pseudofunctor. -/
@[simp]
theorem precomp.obj
    (K : Pseudofunctor A B) (F : Pseudofunctor B D) :
    (precomp D K).obj F = K.comp F := sorry

/-- The `1`-morphism action of functor-bicategory precomposition is precomposition of strong
transformations. -/
@[simp]
theorem precomp.map
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    (η : F ⟶ G) :
    (precomp D K).map η = η.precomp K := sorry

/-- The `2`-morphism action of functor-bicategory precomposition is precomposition of
modifications. -/
@[simp]
theorem precomp.map₂
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) :
    (precomp D K).map₂ Γ = StrongTrans.Hom.precomp Γ K := sorry

/-- A precomposed pseudofunctor acts on objects by applying the original pseudofunctor to
the image under the fixed pseudofunctor. -/
@[simp]
theorem precomp.composite.obj
    (K : Pseudofunctor A B) (F : Pseudofunctor B D) (a : A) :
    ((precomp D K).obj F).obj a = F.obj (K.obj a) := sorry

/-- A precomposed pseudofunctor acts on `1`-morphisms by applying the two pseudofunctors in
sequence. -/
@[simp]
theorem precomp.composite.map
    (K : Pseudofunctor A B) (F : Pseudofunctor B D)
    {a b : A} (f : a ⟶ b) :
    ((precomp D K).obj F).map f = F.map (K.map f) := sorry

/-- A precomposed pseudofunctor acts on `2`-morphisms by applying the two pseudofunctors in
sequence. -/
@[simp]
theorem precomp.composite.map₂
    (K : Pseudofunctor A B) (F : Pseudofunctor B D)
    {a b : A} {f g : a ⟶ b} (γ : f ⟶ g) :
    ((precomp D K).obj F).map₂ γ = F.map₂ (K.map₂ γ) := sorry

/-- The hom-functor of a precomposed pseudofunctor is the composite of the two
hom-functors. -/
@[simp]
theorem precomp.composite.mapFunctor
    (K : Pseudofunctor A B) (F : Pseudofunctor B D) (a b : A) :
    ((precomp D K).obj F).mapFunctor a b =
      K.mapFunctor a b ⋙ F.mapFunctor (K.obj a) (K.obj b) := sorry

/-- The unit comparison of a precomposed pseudofunctor is the image of the first unit
comparison followed by the second unit comparison. -/
@[simp]
theorem precomp.composite.mapId
    (K : Pseudofunctor A B) (F : Pseudofunctor B D) (a : A) :
    ((precomp D K).obj F).mapId a =
      F.map₂Iso (K.mapId a) ≪≫ F.mapId (K.obj a) := sorry

/-- The composition comparison of a precomposed pseudofunctor is the image of the first
composition comparison followed by the second composition comparison. -/
@[simp]
theorem precomp.composite.mapComp
    (K : Pseudofunctor A B) (F : Pseudofunctor B D)
    {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    ((precomp D K).obj F).mapComp f g =
      F.map₂Iso (K.mapComp f g) ≪≫
        F.mapComp (K.map f) (K.map g) := sorry

/-- A precomposed strong transformation has the component of the original transformation at
the image object. -/
@[simp]
theorem precomp.map.app
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    (η : F ⟶ G) (a : A) :
    ((precomp D K).map η).app a = η.app (K.obj a) := sorry

/-- Naturality of a precomposed strong transformation is the original naturality
isomorphism at the image `1`-morphism. -/
@[simp]
theorem precomp.map.naturality
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    (η : F ⟶ G) {a b : A} (f : a ⟶ b) :
    ((precomp D K).map η).naturality f =
      η.naturality (K.map f) := sorry

/-- A precomposed modification has the component of the original modification at the image
object. -/
@[simp]
theorem precomp.map₂.app
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) (a : A) :
    ((precomp D K).map₂ Γ).as.app a =
      Γ.as.app (K.obj a) := sorry

/-- The naturality square of a precomposed modification is the naturality square of the
explicitly precomposed underlying modification. -/
@[simp]
theorem precomp.map₂.naturality
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) {a b : A} (f : a ⟶ b) :
    ((precomp D K).map₂ Γ).as.naturality f =
      (Γ.as.precomp K).naturality f := sorry

end Precomposition

end Pseudofunctor

end CategoryTheory
