module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map.Basic

/-!
# Identity and composition comparisons for categorical pullback maps

This module owns the canonical natural isomorphisms comparing induced pullback maps with identity
and composition, together with their projection computations.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]

namespace Limits.CategoricalPullback

variable {H : X ⥤ Z} {I : Y ⥤ Z} {F : A ⥤ C} {G : B ⥤ C}

/-- Pullback maps respect composition of cospan transformations up to the canonical natural
isomorphism. -/
def mapCompIso
    {D : Type u₇} {E : Type u₈} {K : Type u₉}
    [Category.{v₇} D] [Category.{v₈} E] [Category.{v₉} K]
    {F' : D ⥤ E} {G' : K ⥤ E}
    (ψ : CatCospanTransform H I F G) (ψ' : CatCospanTransform F G F' G') :
    map (ψ.comp ψ') ≅ map ψ ⋙ map ψ' :=
  (CatCommSqOver.toFunctorToCategoricalPullback F' G' (H ⊡ I)).mapIso
    ((CatCommSqOver.transformObjComp (H ⊡ I) ψ ψ').app
      (catCommSqOver H I))

/-- The left projection of the forward composition comparison is the inverse functor
associator on the left legs. -/
@[simp]
theorem mapCompIso.hom.app.fst
    {D : Type u₇} {E : Type u₈} {K : Type u₉}
    [Category.{v₇} D] [Category.{v₈} E] [Category.{v₉} K]
    {F' : D ⥤ E} {G' : K ⥤ E}
    (ψ : CatCospanTransform H I F G) (ψ' : CatCospanTransform F G F' G')
    (P : H ⊡ I) :
    ((mapCompIso ψ ψ').hom.app P).fst =
      (Functor.associator (π₁ H I) ψ.left ψ'.left).inv.app P := sorry

/-- The right projection of the forward composition comparison is the inverse functor
associator on the right legs. -/
@[simp]
theorem mapCompIso.hom.app.snd
    {D : Type u₇} {E : Type u₈} {K : Type u₉}
    [Category.{v₇} D] [Category.{v₈} E] [Category.{v₉} K]
    {F' : D ⥤ E} {G' : K ⥤ E}
    (ψ : CatCospanTransform H I F G) (ψ' : CatCospanTransform F G F' G')
    (P : H ⊡ I) :
    ((mapCompIso ψ ψ').hom.app P).snd =
      (Functor.associator (π₂ H I) ψ.right ψ'.right).inv.app P := sorry

/-- The left projection of the inverse composition comparison is the forward functor
associator on the left legs. -/
@[simp]
theorem mapCompIso.inv.app.fst
    {D : Type u₇} {E : Type u₈} {K : Type u₉}
    [Category.{v₇} D] [Category.{v₈} E] [Category.{v₉} K]
    {F' : D ⥤ E} {G' : K ⥤ E}
    (ψ : CatCospanTransform H I F G) (ψ' : CatCospanTransform F G F' G')
    (P : H ⊡ I) :
    ((mapCompIso ψ ψ').inv.app P).fst =
      (Functor.associator (π₁ H I) ψ.left ψ'.left).hom.app P := sorry

/-- The right projection of the inverse composition comparison is the forward functor
associator on the right legs. -/
@[simp]
theorem mapCompIso.inv.app.snd
    {D : Type u₇} {E : Type u₈} {K : Type u₉}
    [Category.{v₇} D] [Category.{v₈} E] [Category.{v₉} K]
    {F' : D ⥤ E} {G' : K ⥤ E}
    (ψ : CatCospanTransform H I F G) (ψ' : CatCospanTransform F G F' G')
    (P : H ⊡ I) :
    ((mapCompIso ψ ψ').inv.app P).snd =
      (Functor.associator (π₂ H I) ψ.right ψ'.right).hom.app P := sorry

/-- The pullback map induced by the identity cospan transformation is canonically isomorphic
to the identity functor. -/
def mapIdIso :
    map (CatCospanTransform.id H I) ≅ 𝟭 (H ⊡ I) :=
  (CatCommSqOver.toFunctorToCategoricalPullback H I (H ⊡ I)).mapIso
    ((CatCommSqOver.transformObjId (H ⊡ I) H I).app
      (catCommSqOver H I))

/-- The left projection of the forward identity comparison is the right unitor of the first
pullback projection. -/
@[simp]
theorem mapIdIso.hom.app.fst (P : H ⊡ I) :
    ((mapIdIso (H := H) (I := I)).hom.app P).fst =
      (Functor.rightUnitor (π₁ H I)).hom.app P := sorry

/-- The right projection of the forward identity comparison is the right unitor of the second
pullback projection. -/
@[simp]
theorem mapIdIso.hom.app.snd (P : H ⊡ I) :
    ((mapIdIso (H := H) (I := I)).hom.app P).snd =
      (Functor.rightUnitor (π₂ H I)).hom.app P := sorry

/-- The left projection of the inverse identity comparison is the inverse right unitor of the
first pullback projection. -/
@[simp]
theorem mapIdIso.inv.app.fst (P : H ⊡ I) :
    ((mapIdIso (H := H) (I := I)).inv.app P).fst =
      (Functor.rightUnitor (π₁ H I)).inv.app P := sorry

/-- The right projection of the inverse identity comparison is the inverse right unitor of the
second pullback projection. -/
@[simp]
theorem mapIdIso.inv.app.snd (P : H ⊡ I) :
    ((mapIdIso (H := H) (I := I)).inv.app P).snd =
      (Functor.rightUnitor (π₂ H I)).inv.app P := sorry

end Limits.CategoricalPullback

end CategoryTheory

/- Axiom audit: identity and composition comparisons are explicit natural isomorphisms. -/
