/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Induced
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.StrongTrans

/-!
# Extending morphisms along locally equivalent Hom-presheaves

A strong transformation whose maps on canonical Hom-presheaves are local
equivalences admits a canonical extension of every map into a prestack.  The
extension is first exposed as a map of presheaves, then evaluated on the
identity slice and packaged as a functor from the induced category.
-/

@[expose] public section

universe uC vC uP vP

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans

variable {C : Type uC} [Category.{vC} C]
variable {P Q R : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP}}
variable {J : GrothendieckTopology C}

/-- A strong transformation is a local equivalence on Hom-presheaves when each canonical
Hom-presheaf map belongs to the localizing class of the slice topology. -/
def Homwise.IsLocalEquivalence
    (η : P ⟶ Q) (J : GrothendieckTopology C) : Prop :=
  ∀ {U : C} (x y : P.obj (.mk (op U))),
    (J.over U).W (η.presheafHomMap x y)

/-- The canonical extension of a Hom-presheaf map along a strong transformation which is
locally equivalent on Hom-presheaves. -/
noncomputable def Homwise.IsLocalEquivalence.extension
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [hR : R.IsPrestack J]
    {U : C} (x y : P.obj (.mk (op U))) :
    Q.presheafHom
          ((η.app (.mk (op U))).toFunctor.obj x)
          ((η.app (.mk (op U))).toFunctor.obj y) ⟶
      R.presheafHom
          ((θ.app (.mk (op U))).toFunctor.obj x)
          ((θ.app (.mk (op U))).toFunctor.obj y) :=
  (ObjectProperty.isLocal.homEquiv
      (hη x y)
      (R.presheafHom
        ((θ.app (.mk (op U))).toFunctor.obj x)
        ((θ.app (.mk (op U))).toFunctor.obj y))
      (hR.isSheaf
        ((θ.app (.mk (op U))).toFunctor.obj x)
        ((θ.app (.mk (op U))).toFunctor.obj y))).symm
    (θ.presheafHomMap x y)

/-- Precomposition of the canonical Hom extension with the given local equivalence recovers
the original map of Hom-presheaves. -/
theorem Homwise.IsLocalEquivalence.Extension.fac
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J]
    {U : C} (x y : P.obj (.mk (op U))) :
    η.presheafHomMap x y ≫ hη.extension θ x y =
      θ.presheafHomMap x y := sorry

/-- A map of Hom-presheaves with the defining precomposition property is the canonical
extension. -/
theorem Homwise.IsLocalEquivalence.Extension.ext
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J]
    {U : C} (x y : P.obj (.mk (op U)))
    (e :
      Q.presheafHom
          ((η.app (.mk (op U))).toFunctor.obj x)
          ((η.app (.mk (op U))).toFunctor.obj y) ⟶
        R.presheafHom
          ((θ.app (.mk (op U))).toFunctor.obj x)
          ((θ.app (.mk (op U))).toFunctor.obj y))
    (he : η.presheafHomMap x y ≫ e = θ.presheafHomMap x y) :
    e = hη.extension θ x y := sorry

/-- The canonical extension is the unique Hom-presheaf map whose precomposition is the
original strong-transformation map. -/
theorem Homwise.IsLocalEquivalence.Extension.existsUnique
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J]
    {U : C} (x y : P.obj (.mk (op U))) :
    ∃! e :
      Q.presheafHom
          ((η.app (.mk (op U))).toFunctor.obj x)
          ((η.app (.mk (op U))).toFunctor.obj y) ⟶
        R.presheafHom
          ((θ.app (.mk (op U))).toFunctor.obj x)
          ((θ.app (.mk (op U))).toFunctor.obj y),
      η.presheafHomMap x y ≫ e = θ.presheafHomMap x y := sorry

/-- Evaluation of the canonical Hom-presheaf extension on the identity slice, transported
back to a morphism in the target fiber. -/
noncomputable def Homwise.IsLocalEquivalence.Extension.map
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J]
    {U : C} {x y : P.obj (.mk (op U))}
    (f : (η.app (.mk (op U))).toFunctor.obj x ⟶
      (η.app (.mk (op U))).toFunctor.obj y) :
    (θ.app (.mk (op U))).toFunctor.obj x ⟶
      (θ.app (.mk (op U))).toFunctor.obj y :=
  R.presheafHomObjHomEquiv.symm
    ((hη.extension θ x y).app (op (Over.mk (𝟙 U)))
      (Q.presheafHomObjHomEquiv f))

/-- Evaluating the Hom extension after restricting a fiber morphism along a base map is the
restriction of its identity-slice extension. -/
theorem Homwise.IsLocalEquivalence.Extension.appMap
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J]
    {U V : C} (f : V ⟶ U) {x y : P.obj (.mk (op U))}
    (g : (η.app (.mk (op U))).toFunctor.obj x ⟶
      (η.app (.mk (op U))).toFunctor.obj y) :
    (hη.extension θ x y).app (op (Over.mk f))
        ((Q.map f.op.toLoc).toFunctor.map g) =
      (R.map f.op.toLoc).toFunctor.map
        (Homwise.IsLocalEquivalence.Extension.map hη θ g) := sorry

/-- On a morphism in the image of the source category, the extended map agrees with the
given strong transformation. -/
theorem Homwise.IsLocalEquivalence.Extension.Map.onImage
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J]
    {U : C} {x y : P.obj (.mk (op U))} (f : x ⟶ y) :
    Homwise.IsLocalEquivalence.Extension.map hη θ
        ((η.app (.mk (op U))).toFunctor.map f) =
      (θ.app (.mk (op U))).toFunctor.map f := sorry

/-- The extended map preserves identity morphisms between literal image objects. -/
theorem Homwise.IsLocalEquivalence.Extension.Map.id
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J]
    {U : C} (x : P.obj (.mk (op U))) :
    Homwise.IsLocalEquivalence.Extension.map hη θ
        (𝟙 ((η.app (.mk (op U))).toFunctor.obj x)) =
      𝟙 ((θ.app (.mk (op U))).toFunctor.obj x) := sorry

/-- The extended map preserves composition of arbitrary morphisms between literal image
objects. -/
theorem Homwise.IsLocalEquivalence.Extension.Map.comp
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J]
    {U : C} {x y z : P.obj (.mk (op U))}
    (f : (η.app (.mk (op U))).toFunctor.obj x ⟶
      (η.app (.mk (op U))).toFunctor.obj y)
    (g : (η.app (.mk (op U))).toFunctor.obj y ⟶
      (η.app (.mk (op U))).toFunctor.obj z) :
    Homwise.IsLocalEquivalence.Extension.map hη θ (f ≫ g) =
      Homwise.IsLocalEquivalence.Extension.map hη θ f ≫
        Homwise.IsLocalEquivalence.Extension.map hη θ g := sorry

/-- The canonical Hom extension is natural under postcomposition at its target endpoint. -/
theorem Homwise.IsLocalEquivalence.Extension.postcomp
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J]
    {U : C} {x y z : P.obj (.mk (op U))}
    (f : (η.app (.mk (op U))).toFunctor.obj y ⟶
      (η.app (.mk (op U))).toFunctor.obj z) :
    hη.extension θ x y ≫
        Pseudofunctor.PresheafHom.Postcomp.map R
          (Homwise.IsLocalEquivalence.Extension.map hη θ f) =
      Pseudofunctor.PresheafHom.Postcomp.map Q f ≫
        hη.extension θ x z := sorry

/-- The canonical Hom extension is natural under precomposition at its source endpoint. -/
theorem Homwise.IsLocalEquivalence.Extension.precomp
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J]
    {U : C} {x y z : P.obj (.mk (op U))}
    (f : (η.app (.mk (op U))).toFunctor.obj x ⟶
      (η.app (.mk (op U))).toFunctor.obj y) :
    hη.extension θ y z ≫
        Pseudofunctor.PresheafHom.Precomp.map R
          (Homwise.IsLocalEquivalence.Extension.map hη θ f) =
      Pseudofunctor.PresheafHom.Precomp.map Q f ≫
        hη.extension θ x z := sorry

/-- The identity-slice extension sends a commutative square between image objects to a
commutative square in the target. -/
theorem Homwise.IsLocalEquivalence.Extension.Map.square
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J]
    {U : C} {x₁ x₂ y₁ y₂ : P.obj (.mk (op U))}
    (f₁ : (η.app (.mk (op U))).toFunctor.obj x₁ ⟶
      (η.app (.mk (op U))).toFunctor.obj y₁)
    (gₓ : (η.app (.mk (op U))).toFunctor.obj x₁ ⟶
      (η.app (.mk (op U))).toFunctor.obj x₂)
    (gᵧ : (η.app (.mk (op U))).toFunctor.obj y₁ ⟶
      (η.app (.mk (op U))).toFunctor.obj y₂)
    (f₂ : (η.app (.mk (op U))).toFunctor.obj x₂ ⟶
      (η.app (.mk (op U))).toFunctor.obj y₂)
    (h : f₁ ≫ gᵧ = gₓ ≫ f₂) :
    Homwise.IsLocalEquivalence.Extension.map hη θ f₁ ≫
        Homwise.IsLocalEquivalence.Extension.map hη θ gᵧ =
      Homwise.IsLocalEquivalence.Extension.map hη θ gₓ ≫
        Homwise.IsLocalEquivalence.Extension.map hη θ f₂ := sorry

/-- Changing source models by isomorphisms conjugates the identity-slice extension by the
images of those isomorphisms under the target transformation. -/
theorem Homwise.IsLocalEquivalence.Extension.Map.transport
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J]
    {U : C} {x x' y y' : P.obj (.mk (op U))}
    (eₓ : x ≅ x') (eᵧ : y ≅ y')
    (f : (η.app (.mk (op U))).toFunctor.obj x' ⟶
      (η.app (.mk (op U))).toFunctor.obj y') :
    Homwise.IsLocalEquivalence.Extension.map hη θ
        ((η.app (.mk (op U))).toFunctor.map eₓ.hom ≫ f ≫
          (η.app (.mk (op U))).toFunctor.map eᵧ.inv) =
      (θ.app (.mk (op U))).toFunctor.map eₓ.hom ≫
        Homwise.IsLocalEquivalence.Extension.map hη θ f ≫
          (θ.app (.mk (op U))).toFunctor.map eᵧ.inv := sorry

/-- The canonical functor on the category whose objects come from the source and whose
morphisms are computed between their images in the intermediate category. -/
noncomputable def Homwise.IsLocalEquivalence.Extension.functor
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J] (U : C) :
    InducedCategory
        (Q.obj (.mk (op U)))
        (η.app (.mk (op U))).toFunctor.obj ⥤
      R.obj (.mk (op U)) where
  obj x := (θ.app (.mk (op U))).toFunctor.obj x
  map f := Homwise.IsLocalEquivalence.Extension.map hη θ f.hom
  map_id x := Homwise.IsLocalEquivalence.Extension.Map.id hη θ x
  map_comp f g := Homwise.IsLocalEquivalence.Extension.Map.comp hη θ f.hom g.hom

/-- The extension functor sends a morphism to the identity-slice evaluation of the canonical
Hom-presheaf extension. -/
theorem Homwise.IsLocalEquivalence.Extension.Functor.map
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J] (U : C)
    {x y : InducedCategory
      (Q.obj (.mk (op U))) (η.app (.mk (op U))).toFunctor.obj}
    (f : x ⟶ y) :
    (Homwise.IsLocalEquivalence.Extension.functor hη θ U).map f =
      Homwise.IsLocalEquivalence.Extension.map hη θ f.hom := sorry

/-- Restricting the extension functor along the canonical functor into the induced category
recovers the original strong-transformation component. -/
theorem Homwise.IsLocalEquivalence.Extension.Functor.toInducedComp
    {η : P ⟶ Q} (hη : Homwise.IsLocalEquivalence η J)
    (θ : P ⟶ R) [R.IsPrestack J] (U : C) :
    (η.app (.mk (op U))).toFunctor.toInduced ⋙
        Homwise.IsLocalEquivalence.Extension.functor hη θ U =
      (θ.app (.mk (op U))).toFunctor := sorry

end Pseudofunctor.StrongTrans

end CategoryTheory
