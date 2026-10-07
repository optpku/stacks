module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Pseudofunctor.Basic

/-!
# Comparison computations for pseudofunctorial precomposition

Strictness formulas for the identity and composition comparisons of
precomposition in pseudofunctor bicategories.
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

/-- Functor-bicategory precomposition strictly preserves identity strong transformations. -/
@[simp]
theorem precomp.map_id
    (K : Pseudofunctor A B) (F : Pseudofunctor B D) :
    (precomp D K).map (𝟙 F) = StrongTrans.id (K.comp F) := sorry

/-- Functor-bicategory precomposition strictly preserves composition of strong
transformations. -/
@[simp]
theorem precomp.map_comp
    (K : Pseudofunctor A B) {F G H : Pseudofunctor B D}
    (η : F ⟶ G) (θ : G ⟶ H) :
    (precomp D K).map (η ≫ θ) =
      StrongTrans.vcomp (η.precomp K) (θ.precomp K) := sorry

/-- The identity comparison of functor-bicategory precomposition is an identity
isomorphism. -/
@[simp]
theorem precomp.mapId
    (K : Pseudofunctor A B) (F : Pseudofunctor B D) :
    (precomp D K).mapId F =
      Iso.refl ((StrongTrans.id F).precomp K) := sorry

/-- The composition comparison of functor-bicategory precomposition is an identity
isomorphism. -/
@[simp]
theorem precomp.mapComp
    (K : Pseudofunctor A B) {F G H : Pseudofunctor B D}
    (η : F ⟶ G) (θ : G ⟶ H) :
    (precomp D K).mapComp η θ =
      Iso.refl ((StrongTrans.vcomp η θ).precomp K) := sorry

end Precomposition

end Pseudofunctor

end CategoryTheory
