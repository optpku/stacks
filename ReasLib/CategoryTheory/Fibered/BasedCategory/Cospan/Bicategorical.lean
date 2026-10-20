module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Cospan.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Coherence.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Modification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bicategorical specialization of based cospan transformations

This file is the bridge from strong transformations internal to the bicategory of uniformly
sized based categories to the universe-polymorphic `BasedCospanTransform` owner.  The bridge is
one-way: generic pullback functoriality does not depend on bicategorical packaging.
-/

@[expose] public section

namespace CategoryTheory

open BasedFunctor
open scoped Bicategory Pseudofunctor.StrongTrans
open scoped CategoryTheory.Bicategory.CospanTransform

universe u v uB vB w' v' u'

variable {C : Type u} [Category.{v} C]
variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : BasedCategory.{vB, uB} C}
variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}

namespace BasedCospanTransform.Bicategorical

/-- Forget the walking-cospan pseudofunctor packaging of a bicategorical cospan transformation
while retaining its three based functors and two comparison isomorphisms. -/
def obj
    (psi : Bicategory.CospanTransform
      (B := BasedCategory.{vB, uB} C) F₁ G₁ F₂ G₂) :
    BasedCospanTransform F₁ G₁ F₂ G₂ :=
  BasedCospanTransform.mk psi.left psi.right psi.base psi.leftIso psi.rightIso

/-- Forgetting a bicategorical cospan transformation retains its left component. -/
@[simp]
theorem obj.left
    (psi : Bicategory.CospanTransform
      (B := BasedCategory.{vB, uB} C) F₁ G₁ F₂ G₂) :
    (obj psi).left = psi.left := sorry

/-- Forgetting a bicategorical cospan transformation retains its right component. -/
@[simp]
theorem obj.right
    (psi : Bicategory.CospanTransform
      (B := BasedCategory.{vB, uB} C) F₁ G₁ F₂ G₂) :
    (obj psi).right = psi.right := sorry

/-- Forgetting a bicategorical cospan transformation retains its common-target component. -/
@[simp]
theorem obj.base
    (psi : Bicategory.CospanTransform
      (B := BasedCategory.{vB, uB} C) F₁ G₁ F₂ G₂) :
    (obj psi).base = psi.base := sorry

/-- Forgetting a bicategorical cospan transformation retains its left comparison. -/
@[simp]
theorem obj.leftIso
    (psi : Bicategory.CospanTransform
      (B := BasedCategory.{vB, uB} C) F₁ G₁ F₂ G₂) :
    (obj psi).leftIso = psi.leftIso := sorry

/-- Forgetting a bicategorical cospan transformation retains its right comparison. -/
@[simp]
theorem obj.rightIso
    (psi : Bicategory.CospanTransform
      (B := BasedCategory.{vB, uB} C) F₁ G₁ F₂ G₂) :
    (obj psi).rightIso = psi.rightIso := sorry

/-- Forgetting the identity bicategorical cospan transformation gives the generic identity
transformation. -/
theorem obj.id (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) :
    obj (Bicategory.CospanTransform.id
      (B := BasedCategory.{vB, uB} C) F G) =
      BasedCospanTransform.id F G := sorry

/-- Forgetting vertical composition of bicategorical cospan transformations gives vertical
composition in the generic owner. -/
theorem obj.comp
    {X₃ Y₃ S₃ : BasedCategory.{vB, uB} C}
    {F₃ : X₃ ⥤ᵇ S₃} {G₃ : Y₃ ⥤ᵇ S₃}
    (psi : Bicategory.CospanTransform
      (B := BasedCategory.{vB, uB} C) F₁ G₁ F₂ G₂)
    (phi : Bicategory.CospanTransform
      (B := BasedCategory.{vB, uB} C) F₂ G₂ F₃ G₃) :
    obj (psi.comp phi) = (obj psi).comp (obj phi) := sorry

variable {psi phi chi : Bicategory.CospanTransform
  (B := BasedCategory.{vB, uB} C) F₁ G₁ F₂ G₂}

/-- The three components of a bicategorical modification satisfy the generic left naturality
equation after forgetting the walking-cospan packaging. -/
theorem map.leftNaturality (alpha : Pseudofunctor.StrongTrans.Hom psi phi) :
    BasedCategory.whiskerRight (Bicategory.CospanTransform.Hom.left alpha) F₂ ≫
        (obj phi).leftIso.hom =
      (obj psi).leftIso.hom ≫
        BasedCategory.whiskerLeft F₁
          (Bicategory.CospanTransform.Hom.base alpha) := sorry

/-- The three components of a bicategorical modification satisfy the generic right naturality
equation after forgetting the walking-cospan packaging. -/
theorem map.rightNaturality (alpha : Pseudofunctor.StrongTrans.Hom psi phi) :
    BasedCategory.whiskerRight (Bicategory.CospanTransform.Hom.right alpha) G₂ ≫
        (obj phi).rightIso.hom =
      (obj psi).rightIso.hom ≫
        BasedCategory.whiskerLeft G₁
          (Bicategory.CospanTransform.Hom.base alpha) := sorry

/-- Forget a bicategorical modification to a modification between the generic based cospan
transformations. -/
def map (alpha : Pseudofunctor.StrongTrans.Hom psi phi) :
    BasedCospanTransform.Hom (obj psi) (obj phi) :=
  BasedCospanTransform.Hom.mk
    (Bicategory.CospanTransform.Hom.left alpha)
    (Bicategory.CospanTransform.Hom.right alpha)
    (Bicategory.CospanTransform.Hom.base alpha)
    (map.leftNaturality alpha) (map.rightNaturality alpha)

/-- Forgetting a bicategorical modification retains its left endpoint component. -/
@[simp]
theorem map.left (alpha : Pseudofunctor.StrongTrans.Hom psi phi) :
    (map alpha).left = Bicategory.CospanTransform.Hom.left alpha := sorry

/-- Forgetting a bicategorical modification retains its right endpoint component. -/
@[simp]
theorem map.right (alpha : Pseudofunctor.StrongTrans.Hom psi phi) :
    (map alpha).right = Bicategory.CospanTransform.Hom.right alpha := sorry

/-- Forgetting a bicategorical modification retains its common-target component. -/
@[simp]
theorem map.base (alpha : Pseudofunctor.StrongTrans.Hom psi phi) :
    (map alpha).base = Bicategory.CospanTransform.Hom.base alpha := sorry

/-- Forgetting an identity bicategorical modification gives the identity generic
modification. -/
@[simp]
theorem map.id (psi : Bicategory.CospanTransform
    (B := BasedCategory.{vB, uB} C) F₁ G₁ F₂ G₂) :
    map (𝟙 psi) = 𝟙 (obj psi) := sorry

/-- Forgetting vertical composition of bicategorical modifications preserves composition. -/
@[simp]
theorem map.comp (alpha : psi ⟶ phi) (beta : phi ⟶ chi) :
    map (alpha ≫ beta) =
      BasedCospanTransform.Hom.comp (map alpha) (map beta) := sorry

/-- The forgetful bridge from bicategorical cospan transformations and modifications to their
universe-polymorphic based counterparts. -/
def functor :
    Bicategory.CospanTransform
        (B := BasedCategory.{vB, uB} C) F₁ G₁ F₂ G₂ ⥤
      BasedCospanTransform F₁ G₁ F₂ G₂ where
  obj := obj
  map := map
  map_id := map.id
  map_comp := fun alpha beta => map.comp alpha beta

/-- The object action of the bicategorical-to-generic forgetful functor is `obj`. -/
@[simp]
theorem functor.obj
    (psi : Bicategory.CospanTransform
      (B := BasedCategory.{vB, uB} C) F₁ G₁ F₂ G₂) :
    functor.obj psi = obj psi := sorry

/-- The morphism action of the bicategorical-to-generic forgetful functor is `map`. -/
@[simp]
theorem functor.map (alpha : psi ⟶ phi) :
    functor.map alpha = map alpha := sorry

/-- Forget an isomorphism of bicategorical cospan transformations to an isomorphism of generic
based cospan transformations. -/
def mapIso (e : psi ≅ phi) : obj psi ≅ obj phi :=
  functor.mapIso e

/-- The forward map of a forgotten bicategorical cospan isomorphism is the forgotten forward
modification. -/
@[simp]
theorem mapIso.hom (e : psi ≅ phi) :
    (mapIso e).hom = map e.hom := sorry

/-- The inverse map of a forgotten bicategorical cospan isomorphism is the forgotten inverse
modification. -/
@[simp]
theorem mapIso.inv (e : psi ≅ phi) :
    (mapIso e).inv = map e.inv := sorry

section MapCoherence

variable {B : Type u'} [Bicategory.{w', v'} B]
variable {x y z x' y' z' x'' y'' z'' : B}
variable {f : x ⟶ z} {g : y ⟶ z}
variable {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {f'' : x'' ⟶ z''} {g'' : y'' ⟶ z''}

/-- After mapping a bicategorical identity cospan transformation into based categories,
forgetting the bicategorical packaging is canonically isomorphic to the generic identity
based cospan transformation. -/
@[stacks 0040 "generic based identity comparison after mapping a bicategorical cospan"]
def mapIdIso (f : x ⟶ z) (g : y ⟶ z)
    (P : B ⥤ᵖ BasedCategory.{vB, uB} C) :
    obj ((Bicategory.CospanTransform.id f g).map P) ≅
      BasedCospanTransform.id (P.map f) (P.map g) :=
  mapIso (Bicategory.CospanTransform.map.idIso f g P) ≪≫
    eqToIso (obj.id (P.map f) (P.map g))

/-- After mapping a composite bicategorical cospan transformation into based categories,
forgetting the bicategorical packaging is canonically isomorphic to the composite of the two
generic forgotten transformations. -/
@[stacks 0040 "generic based composition comparison after mapping bicategorical cospans"]
def mapCompIso
    (psi : Bicategory.CospanTransform f g f' g')
    (phi : Bicategory.CospanTransform f' g' f'' g'')
    (P : B ⥤ᵖ BasedCategory.{vB, uB} C) :
    obj ((psi.comp phi).map P) ≅
      (obj (psi.map P)).comp (obj (phi.map P)) :=
  mapIso (Bicategory.CospanTransform.map.compIso psi phi P) ≪≫
    eqToIso (obj.comp (psi.map P) (phi.map P))

end MapCoherence

end BasedCospanTransform.Bicategorical

namespace Bicategory.Cospan.Hom

variable {R S T : Bicategory.Cospan (BasedCategory.{vB, uB} C)}

/-- Forget a morphism of bundled based cospans directly to the universe-polymorphic based
cospan transformation carried by its three vertex maps. -/
def toBasedTransform (psi : S ⟶ T) :
  BasedCospanTransform S.fst S.snd T.fst T.snd :=
  BasedCospanTransform.Bicategorical.obj
    (Bicategory.Cospan.Hom.toCospanTransform psi)

/-- Forgetting the identity morphism of a bundled cospan gives the generic identity cospan
transformation. -/
@[simp]
theorem toBasedTransform.id (S : Bicategory.Cospan (BasedCategory.{vB, uB} C)) :
    toBasedTransform (𝟙 S) = BasedCospanTransform.id S.fst S.snd := sorry

/-- Forgetting a composite of bundled cospan morphisms gives the composite of their generic
based cospan transformations. -/
@[simp]
theorem toBasedTransform.comp (psi : R ⟶ S) (phi : S ⟶ T) :
    toBasedTransform (psi ≫ phi) =
      (toBasedTransform psi).comp (toBasedTransform phi) := sorry

end Bicategory.Cospan.Hom

namespace Bicategory.Cospan.Hom₂

variable {S T : Bicategory.Cospan (BasedCategory.{vB, uB} C)}
variable {psi phi chi : S ⟶ T}

/-- Forget a `2`-morphism of bundled based cospans directly to a modification of the generic
based cospan transformations. -/
def toBasedModification (alpha : psi ⟶ phi) :
    BasedCospanTransform.Hom
      (Bicategory.Cospan.Hom.toBasedTransform psi)
      (Bicategory.Cospan.Hom.toBasedTransform phi) :=
  BasedCospanTransform.Bicategorical.map
    (Bicategory.Cospan.Hom₂.toModification alpha)

/-- Forgetting an identity bundled cospan `2`-morphism gives the identity generic
modification. -/
@[simp]
theorem toBasedModification.id (psi : S ⟶ T) :
    toBasedModification (𝟙 psi) =
      BasedCospanTransform.Hom.id
        (Bicategory.Cospan.Hom.toBasedTransform psi) := sorry

/-- Forgetting vertical composition of bundled cospan `2`-morphisms preserves vertical
composition of generic modifications. -/
@[simp]
theorem toBasedModification.comp (alpha : psi ⟶ phi) (beta : phi ⟶ chi) :
    toBasedModification (alpha ≫ beta) =
      BasedCospanTransform.Hom.comp
        (toBasedModification alpha) (toBasedModification beta) := sorry

end Bicategory.Cospan.Hom₂

namespace Bicategory.Cospan

/-- The direct forgetful functor from a bundled-cospan hom category to the generic category of
universe-polymorphic based cospan transformations. -/
def basedTransformFunctor
    (S T : Bicategory.Cospan (BasedCategory.{vB, uB} C)) :
    (S ⟶ T) ⥤ BasedCospanTransform S.fst S.snd T.fst T.snd where
  obj := Hom.toBasedTransform
  map := Hom₂.toBasedModification
  map_id := Hom₂.toBasedModification.id
  map_comp := Hom₂.toBasedModification.comp

/-- The object action of the direct bundled-to-generic cospan functor is
`Hom.toBasedTransform`. -/
@[simp]
theorem basedTransformFunctor.obj
    (S T : Bicategory.Cospan (BasedCategory.{vB, uB} C)) (psi : S ⟶ T) :
    (basedTransformFunctor S T).obj psi = Hom.toBasedTransform psi := sorry

/-- The morphism action of the direct bundled-to-generic cospan functor is
`Hom₂.toBasedModification`. -/
@[simp]
theorem basedTransformFunctor.map
    (S T : Bicategory.Cospan (BasedCategory.{vB, uB} C))
    {psi phi : S ⟶ T} (alpha : psi ⟶ phi) :
    (basedTransformFunctor S T).map alpha = Hom₂.toBasedModification alpha := sorry

end Bicategory.Cospan

end CategoryTheory
