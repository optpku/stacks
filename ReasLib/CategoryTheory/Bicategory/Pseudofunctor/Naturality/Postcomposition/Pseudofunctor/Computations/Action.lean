module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Pseudofunctor.Basic

/-!
# Action computations for pseudofunctorial postcomposition

Object, `1`-morphism, and `2`-morphism formulas for the postcomposition
pseudofunctor and the pseudofunctors it produces.
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

/-- The object action of functor-bicategory postcomposition is composition with the fixed
pseudofunctor. -/
@[simp]
theorem postcomp.obj
    (K : Pseudofunctor B D) (F : Pseudofunctor A B) :
    (postcomp A K).obj F = F.comp K := sorry

/-- The `1`-morphism action of functor-bicategory postcomposition is postcomposition of strong
transformations. -/
@[simp]
theorem postcomp.map
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    (η : F ⟶ G) :
    (postcomp A K).map η = η.postcomp K := sorry

/-- The `2`-morphism action of functor-bicategory postcomposition is postcomposition of
modifications. -/
@[simp]
theorem postcomp.map₂
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) :
    (postcomp A K).map₂ Γ =
      StrongTrans.Hom.postcomp Γ K := sorry

/-- A postcomposed pseudofunctor acts on objects by applying the two pseudofunctors in
sequence. -/
@[simp]
theorem postcomp.composite.obj
    (K : Pseudofunctor B D) (F : Pseudofunctor A B) (a : A) :
    ((postcomp A K).obj F).obj a = K.obj (F.obj a) := sorry

/-- A postcomposed pseudofunctor acts on `1`-morphisms by applying the two pseudofunctors in
sequence. -/
@[simp]
theorem postcomp.composite.map
    (K : Pseudofunctor B D) (F : Pseudofunctor A B)
    {a b : A} (f : a ⟶ b) :
    ((postcomp A K).obj F).map f = K.map (F.map f) := sorry

/-- A postcomposed pseudofunctor acts on `2`-morphisms by applying the two pseudofunctors in
sequence. -/
@[simp]
theorem postcomp.composite.map₂
    (K : Pseudofunctor B D) (F : Pseudofunctor A B)
    {a b : A} {f g : a ⟶ b} (γ : f ⟶ g) :
    ((postcomp A K).obj F).map₂ γ =
      K.map₂ (F.map₂ γ) := sorry

/-- The hom-functor of a postcomposed pseudofunctor is the composite of the two
hom-functors. -/
@[simp]
theorem postcomp.composite.mapFunctor
    (K : Pseudofunctor B D) (F : Pseudofunctor A B) (a b : A) :
    ((postcomp A K).obj F).mapFunctor a b =
      F.mapFunctor a b ⋙
        K.mapFunctor (F.obj a) (F.obj b) := sorry

/-- The unit comparison of a postcomposed pseudofunctor is the image of the first unit
comparison followed by the second unit comparison. -/
@[simp]
theorem postcomp.composite.mapId
    (K : Pseudofunctor B D) (F : Pseudofunctor A B) (a : A) :
    ((postcomp A K).obj F).mapId a =
      K.map₂Iso (F.mapId a) ≪≫ K.mapId (F.obj a) := sorry

/-- The composition comparison of a postcomposed pseudofunctor is the image of the first
composition comparison followed by the second composition comparison. -/
@[simp]
theorem postcomp.composite.mapComp
    (K : Pseudofunctor B D) (F : Pseudofunctor A B)
    {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    ((postcomp A K).obj F).mapComp f g =
      K.map₂Iso (F.mapComp f g) ≪≫
        K.mapComp (F.map f) (F.map g) := sorry

/-- A postcomposed strong transformation has the image under the fixed pseudofunctor of the
original component. -/
@[simp]
theorem postcomp.map.app
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    (η : F ⟶ G) (a : A) :
    ((postcomp A K).map η).app a =
      K.map (η.app a) := sorry

/-- Naturality of a postcomposed strong transformation is the mapped naturality isomorphism
conjugated by the fixed pseudofunctor's composition comparisons. -/
@[simp]
theorem postcomp.map.naturality
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    (η : F ⟶ G) {a b : A} (f : a ⟶ b) :
    ((postcomp A K).map η).naturality f =
      (K.mapComp (F.map f) (η.app b)).symm ≪≫
        K.map₂Iso (η.naturality f) ≪≫
          K.mapComp (η.app a) (G.map f) := sorry

/-- A postcomposed modification has the image under the fixed pseudofunctor of the original
component. -/
@[simp]
theorem postcomp.map₂.app
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) (a : A) :
    ((postcomp A K).map₂ Γ).as.app a =
      K.map₂ (Γ.as.app a) := sorry

/-- The naturality square of a postcomposed modification is the naturality square of the
explicitly postcomposed underlying modification. -/
@[simp]
theorem postcomp.map₂.naturality
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) {a b : A} (f : a ⟶ b) :
    ((postcomp A K).map₂ Γ).as.naturality f =
      (Γ.as.postcomp K).naturality f := sorry

end Postcomposition

end Pseudofunctor

end CategoryTheory
