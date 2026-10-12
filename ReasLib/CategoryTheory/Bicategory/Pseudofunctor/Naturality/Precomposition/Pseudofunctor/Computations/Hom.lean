/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Pseudofunctor.Basic

/-!
# Hom-functor computations for pseudofunctorial precomposition

Pointwise formulas for the induced functor on strong-transformation
hom-categories.
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

/-- The object action of `precompHom` has pointwise evaluated strong-transformation
components. -/
@[simp]
theorem precompHom.obj.app
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    (η : F ⟶ G) (a : A) :
    ((precompHom K F G).obj η).app a = η.app (K.obj a) := sorry

/-- The object action of `precompHom` evaluates strong-transformation naturality at the
image `1`-morphism. -/
@[simp]
theorem precompHom.obj.naturality
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    (η : F ⟶ G) {a b : A} (f : a ⟶ b) :
    ((precompHom K F G).obj η).naturality f =
      η.naturality (K.map f) := sorry

/-- The morphism action of `precompHom` has pointwise evaluated modification components. -/
@[simp]
theorem precompHom.map.app
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) (a : A) :
    ((precompHom K F G).map Γ).as.app a = Γ.as.app (K.obj a) := sorry

/-- The morphism action of `precompHom` is the explicitly precomposed modification. -/
@[simp]
theorem precompHom.map.naturality
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) {a b : A} (f : a ⟶ b) :
    ((precompHom K F G).map Γ).as.naturality f =
      (Γ.as.precomp K).naturality f := sorry

/-- The hom-functor of functor-bicategory precomposition is the explicit precomposition
functor on strong transformations and modifications. -/
@[simp]
theorem precomp.mapFunctor
    (K : Pseudofunctor A B) (F G : Pseudofunctor B D) :
    (precomp D K).mapFunctor F G = precompHom K F G := sorry

end Precomposition

end Pseudofunctor

end CategoryTheory
