/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Internal Hom for Type-valued sheaves

Mathlib defines the localized presheaf `presheafHom F G` and the corresponding
sheaf `sheafHom F G`. This module supplies the comparison with the internal Hom
of the functor category and the resulting cartesian-closed API for Type-valued
sheaves. The constructions are independent of a particular chapter or site
presentation.
-/

@[expose] public section

open CategoryTheory Limits CartesianMonoidalCategory Opposite
open scoped CartesianClosed

universe u v

noncomputable section

namespace CategoryTheory.Presheaf.Hom

variable {C : Type u} [Category.{v} C]

/-- The functor-category closed structure whose internal Hom is definitionally
`Functor.functorHom`. It is scoped to avoid competing globally with Mathlib's
extensionally equivalent same-universe construction. -/
scoped instance functorToTypesClosed : MonoidalClosed (Cᵒᵖ ⥤ Type (max u v)) :=
  FunctorToTypes.monoidalClosed

end CategoryTheory.Presheaf.Hom

namespace CategoryTheory.Presheaf.Hom.Functor

variable {C : Type u} [Category.{v} C]

/-- The co-Yoneda test functor underlying a section of `F.functorHom G` at `X`. -/
abbrev coYonedaUnop (X : Cᵒᵖ) : Cᵒᵖ ⥤ Type v :=
  (coyoneda.rightOp.obj X).unop

/-- The explicit forward objectwise map from localized morphisms to functor-category internal
Hom data. -/
def toApp
    (F G : Cᵒᵖ ⥤ Type (max u v)) (X : Cᵒᵖ) (alpha : (presheafHom F G).obj X) :
    ∀ (Y : Cᵒᵖ), (coYonedaUnop X).obj Y → (F.obj Y ⟶ G.obj Y) :=
  fun _ f ↦ alpha.app (op (Over.mk (Quiver.Hom.unop f)))

/-- The forward objectwise map respects the functor-category naturality condition. -/
theorem toAppNaturality
    (F G : Cᵒᵖ ⥤ Type (max u v)) (X : Cᵒᵖ) (alpha : (presheafHom F G).obj X) :
    ∀ {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (a : (coYonedaUnop X).obj Y),
      F.map f ≫ toApp F G X alpha Z ((coYonedaUnop X).map f a) =
        toApp F G X alpha Y a ≫ G.map f := sorry

/-- The forward map from localized morphisms to functor-category internal Hom data. -/
def toFunctorHom
    (F G : Cᵒᵖ ⥤ Type (max u v)) (X : Cᵒᵖ) (alpha : (presheafHom F G).obj X) :
    (F.functorHom G).obj X :=
  { app := toApp F G X alpha
    naturality := toAppNaturality F G X alpha }

/-- The explicit backward objectwise map from functor-category internal Hom data to localized
morphisms. -/
def fromApp
    (F G : Cᵒᵖ ⥤ Type (max u v)) (X : Cᵒᵖ) (alpha : (F.functorHom G).obj X)
    (Y : (Over X.unop)ᵒᵖ) :
    ((Over.forget X.unop).op ⋙ F).obj Y ⟶ ((Over.forget X.unop).op ⋙ G).obj Y :=
  match Y with
  | op Y => alpha.app (op Y.left) Y.hom.op

/-- The backward objectwise map respects the naturality condition over `Over X.unop`. -/
theorem fromAppNaturality
    (F G : Cᵒᵖ ⥤ Type (max u v)) (X : Cᵒᵖ) (alpha : (F.functorHom G).obj X) :
    ∀ ⦃Y Z : (Over X.unop)ᵒᵖ⦄ (f : Y ⟶ Z),
      ((Over.forget X.unop).op ⋙ F).map f ≫ fromApp F G X alpha Z =
        fromApp F G X alpha Y ≫ ((Over.forget X.unop).op ⋙ G).map f := sorry

/-- The backward map from functor-category internal Hom data to localized morphisms. -/
def fromFunctorHom
    (F G : Cᵒᵖ ⥤ Type (max u v)) (X : Cᵒᵖ) (alpha : (F.functorHom G).obj X) :
    (presheafHom F G).obj X :=
  { app := fromApp F G X alpha
    naturality := fromAppNaturality F G X alpha }

/-- The backward map is a left inverse to the forward map. -/
theorem leftInv
    (F G : Cᵒᵖ ⥤ Type (max u v)) (X : Cᵒᵖ) (alpha : (presheafHom F G).obj X) :
    fromFunctorHom F G X (toFunctorHom F G X alpha) = alpha := sorry

/-- The forward map is a right inverse to the backward map. -/
theorem rightInv
    (F G : Cᵒᵖ ⥤ Type (max u v)) (X : Cᵒᵖ) (alpha : (F.functorHom G).obj X) :
    toFunctorHom F G X (fromFunctorHom F G X alpha) = alpha := sorry

/-- The objectwise equivalence between localized morphisms and functor-category internal Hom
data. -/
def equiv
    (F G : Cᵒᵖ ⥤ Type (max u v)) (X : Cᵒᵖ) :
    (presheafHom F G).obj X ≃ (F.functorHom G).obj X where
  toFun := toFunctorHom F G X
  invFun := fromFunctorHom F G X
  left_inv := leftInv F G X
  right_inv := rightInv F G X

/-- The objectwise equivalences assemble naturally in the site object. -/
theorem equivNaturality
    (F G : Cᵒᵖ ⥤ Type (max u v)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (presheafHom F G).map f ≫ (equiv F G Y).toIso.hom =
      (equiv F G X).toIso.hom ≫ (F.functorHom G).map f := sorry

end CategoryTheory.Presheaf.Hom.Functor

namespace CategoryTheory.Presheaf.Hom

variable {C : Type u} [Category.{v} C]

/-- The localized Hom presheaf `presheafHom F G` is canonically the internal Hom
`F.functorHom G` of the functor category. -/
def functorHomIso (F G : Cᵒᵖ ⥤ Type (max u v)) :
    presheafHom F G ≅ F.functorHom G :=
  NatIso.ofComponents
    (fun X ↦ (Functor.equiv F G X).toIso)
    (Functor.equivNaturality F G)

end CategoryTheory.Presheaf.Hom

namespace CategoryTheory.Sheaf.Hom.Functor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The Type-valued sheaf closed structure induced by the `FunctorToTypes` presentation.
The local instance in its construction is a defeq pin: it selects the functor-category internal
Hom `Functor.functorHom` without changing global typeclass search. -/
@[reducible] noncomputable def monoidalClosed : MonoidalClosed (Sheaf J (Type (max u v))) :=
  -- Local instance justification (defeq pin): select the closed structure with internal Hom definitionally `Functor.functorHom`.
  letI : MonoidalClosed (Cᵒᵖ ⥤ Type (max u v)) := Presheaf.Hom.functorToTypesClosed
  inferInstance

/-- The internal-Hom functor associated to `monoidalClosed`. -/
noncomputable def ihom (G : Sheaf J (Type (max u v))) :
    Sheaf J (Type (max u v)) ⥤ Sheaf J (Type (max u v)) :=
  @CategoryTheory.ihom (Sheaf J (Type (max u v))) _ _ G
    (@MonoidalClosed.closed (Sheaf J (Type (max u v))) _ _ monoidalClosed G)

/-- The tensor/internal-Hom adjunction associated to the functor-Hom presentation. -/
noncomputable def adjunction (G : Sheaf J (Type (max u v))) :
    MonoidalCategory.tensorLeft G ⊣ ihom G :=
  -- Local instance justification (defeq pin): keep the adjunction definitionally aligned with the named `monoidalClosed` presentation.
  letI : MonoidalClosed (Sheaf J (Type (max u v))) := monoidalClosed
  CategoryTheory.ihom.adjunction G

/-- The internal Hom of `adjunction G` is canonically the localized morphism sheaf
`sheafHom G H`. -/
noncomputable def ihomIso (G H : Sheaf J (Type (max u v))) :
    (ihom G).obj H ≅ sheafHom G H :=
  -- Local instance justification (defeq pin): identify the internal Hom with the `monoidalClosed` presentation used above.
  letI : MonoidalClosed (Sheaf J (Type (max u v))) := monoidalClosed
  (fullyFaithfulSheafToPresheaf J (Type (max u v))).preimageIso
    ((Presheaf.Hom.functorHomIso G.obj H.obj).symm ≪≫ (sheafHom'Iso G H).symm)

end CategoryTheory.Sheaf.Hom.Functor

namespace CategoryTheory.Sheaf.Hom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Currying for Type-valued sheaves, expressed through Mathlib's localized sheaf-Hom object
and the explicit `Functor` closed presentation. -/
def curryEquiv (F G H : Sheaf J (Type (max u v))) :
    ((F ⨯ G) ⟶ H) ≃ (F ⟶ sheafHom G H) :=
  (((prod.braiding F G).homCongr (Iso.refl H)).trans
      ((((tensorLeftIsoProd G).app F).symm.homCongr (Iso.refl H)).trans
        ((CategoryTheory.Sheaf.Hom.Functor.adjunction G).homEquiv F H))).trans
    ((Iso.refl F).homCongr (CategoryTheory.Sheaf.Hom.Functor.ihomIso G H))

/-- Evaluation of the localized sheaf-Hom, obtained by uncurrying its identity morphism. -/
noncomputable def eval
    (G H : Sheaf J (Type (max u v))) : G ⨯ sheafHom G H ⟶ H :=
  (prod.braiding G (sheafHom G H)).hom ≫
    (curryEquiv (sheafHom G H) G H).symm (𝟙 (sheafHom G H))

end CategoryTheory.Sheaf.Hom
