module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Pseudofunctor.Basic

/-!
# Comparison computations for pseudofunctorial postcomposition

Pointwise formulas for the identity and composition comparisons of
postcomposition in pseudofunctor bicategories.
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

/-- The forward component of the postcomposition identity comparison is the forward identity
comparison of the fixed pseudofunctor. -/
@[simp]
theorem postcompMapId.hom_app
    (K : Pseudofunctor B D) (F : Pseudofunctor A B) (a : A) :
    (postcompMapId K F).hom.as.app a =
      (K.mapId (F.obj a)).hom := sorry

/-- The inverse component of the postcomposition identity comparison is the inverse identity
comparison of the fixed pseudofunctor. -/
@[simp]
theorem postcompMapId.inv_app
    (K : Pseudofunctor B D) (F : Pseudofunctor A B) (a : A) :
    (postcompMapId K F).inv.as.app a =
      (K.mapId (F.obj a)).inv := sorry

/-- The forward component of the postcomposition composition comparison is the forward
composition comparison of the fixed pseudofunctor. -/
@[simp]
theorem postcompMapComp.hom_app
    (K : Pseudofunctor B D)
    {F G H : Pseudofunctor A B} (η : F ⟶ G) (θ : G ⟶ H)
    (a : A) :
    (postcompMapComp K η θ).hom.as.app a =
      (K.mapComp (η.app a) (θ.app a)).hom := sorry

/-- The inverse component of the postcomposition composition comparison is the inverse
composition comparison of the fixed pseudofunctor. -/
@[simp]
theorem postcompMapComp.inv_app
    (K : Pseudofunctor B D)
    {F G H : Pseudofunctor A B} (η : F ⟶ G) (θ : G ⟶ H)
    (a : A) :
    (postcompMapComp K η θ).inv.as.app a =
      (K.mapComp (η.app a) (θ.app a)).inv := sorry

/-- The identity comparison of functor-bicategory postcomposition is the explicit pointwise
identity comparison. -/
@[simp]
theorem postcomp.mapId
    (K : Pseudofunctor B D) (F : Pseudofunctor A B) :
    (postcomp A K).mapId F = postcompMapId K F := sorry

/-- The composition comparison of functor-bicategory postcomposition is the explicit
pointwise composition comparison. -/
@[simp]
theorem postcomp.mapComp
    (K : Pseudofunctor B D)
    {F G H : Pseudofunctor A B} (η : F ⟶ G) (θ : G ⟶ H) :
    (postcomp A K).mapComp η θ =
      postcompMapComp K η θ := sorry

/-- The forward component of the postcomposition unit comparison is the pointwise forward
unit comparison of the fixed pseudofunctor. -/
@[simp]
theorem postcomp.mapId.hom_app
    (K : Pseudofunctor B D) (F : Pseudofunctor A B) (a : A) :
    ((postcomp A K).mapId F).hom.as.app a =
      (K.mapId (F.obj a)).hom := sorry

/-- The inverse component of the postcomposition unit comparison is the pointwise inverse
unit comparison of the fixed pseudofunctor. -/
@[simp]
theorem postcomp.mapId.inv_app
    (K : Pseudofunctor B D) (F : Pseudofunctor A B) (a : A) :
    ((postcomp A K).mapId F).inv.as.app a =
      (K.mapId (F.obj a)).inv := sorry

/-- The forward component of the postcomposition composition comparison is the pointwise
forward composition comparison of the fixed pseudofunctor. -/
@[simp]
theorem postcomp.mapComp.hom_app
    (K : Pseudofunctor B D)
    {F G H : Pseudofunctor A B} (η : F ⟶ G) (θ : G ⟶ H)
    (a : A) :
    ((postcomp A K).mapComp η θ).hom.as.app a =
      (K.mapComp (η.app a) (θ.app a)).hom := sorry

/-- The inverse component of the postcomposition composition comparison is the pointwise
inverse composition comparison of the fixed pseudofunctor. -/
@[simp]
theorem postcomp.mapComp.inv_app
    (K : Pseudofunctor B D)
    {F G H : Pseudofunctor A B} (η : F ⟶ G) (θ : G ⟶ H)
    (a : A) :
    ((postcomp A K).mapComp η θ).inv.as.app a =
      (K.mapComp (η.app a) (θ.app a)).inv := sorry

end Postcomposition

end Pseudofunctor

end CategoryTheory
