module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Products of Object Properties

This file provides the objectwise product of two properties and the induced equivalence between
its full subcategory and the product of the two full subcategories.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.ObjectProperty

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- The object property on a product category requiring the corresponding property in each
factor. -/
@[stacks 001K "product object property"]
def prod (P : ObjectProperty C) (Q : ObjectProperty D) : ObjectProperty (C × D) :=
  fun X ↦ P X.1 ∧ Q X.2

/-- Membership in a product object property is componentwise membership. -/
@[simp, stacks 001K "product object property membership"]
theorem prod_iff (P : ObjectProperty C) (Q : ObjectProperty D) (X : C × D) :
    P.prod Q X ↔ P X.1 ∧ Q X.2 := Iff.rfl

/-- A product object property is closed under isomorphisms when both factor properties are. -/
@[stacks 001K "product object property isomorphism closure"]
instance prod.isClosedUnderIsomorphisms (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms] :
    (P.prod Q).IsClosedUnderIsomorphisms where
  of_iso e h :=
    ⟨P.prop_of_iso ((CategoryTheory.Prod.fst C D).mapIso e) h.1,
      Q.prop_of_iso ((CategoryTheory.Prod.snd C D).mapIso e) h.2⟩

/-- Equality of an inverse-image product property is equivalent to its objectwise formulation.
-/
@[stacks 001K "product object property inverse image criterion"]
theorem inverseImage_prod_eq_iff (F : C ⥤ D × E) (P : ObjectProperty C)
    (Q : ObjectProperty D) (T : ObjectProperty E) :
    (Q.prod T).inverseImage F = P ↔
      ∀ X, P X ↔ Q (F.obj X).1 ∧ T (F.obj X).2 := by
  constructor
  · intro h X
    rw [← h]
    rfl
  · intro h
    funext X
    exact propext (h X).symm

namespace FullSubcategory

/-- The full subcategory of a product object property is equivalent to the product of the two
factor full subcategories. -/
@[stacks 001K "product object property full subcategory equivalence"]
def prodEquivalence (P : ObjectProperty C) (Q : ObjectProperty D) :
    (P.prod Q).FullSubcategory ≌ P.FullSubcategory × Q.FullSubcategory :=
  let F :=
    (P.lift ((P.prod Q).ι ⋙ CategoryTheory.Prod.fst C D) (fun X ↦ X.property.1)).prod'
      (Q.lift ((P.prod Q).ι ⋙ CategoryTheory.Prod.snd C D) (fun X ↦ X.property.2))
  let G :=
    (P.prod Q).lift (Functor.prod P.ι Q.ι)
      (fun X ↦ ⟨X.1.property, X.2.property⟩)
  CategoryTheory.Equivalence.mk F G
    (NatIso.ofComponents (fun X ↦
        ObjectProperty.isoMk (P := P.prod Q) (CategoryTheory.prod.etaIso X.obj))
      (fun f ↦ ObjectProperty.hom_ext _ (by
        apply Prod.hom_ext
        · exact (Category.comp_id _).trans (Category.id_comp _).symm
        · exact (Category.comp_id _).trans (Category.id_comp _).symm)))
    (NatIso.ofComponents (fun X ↦
        Iso.prod
          (ObjectProperty.isoMk (P := P) (Iso.refl X.1.obj))
          (ObjectProperty.isoMk (P := Q) (Iso.refl X.2.obj)) ≪≫ CategoryTheory.prod.etaIso X)
      (fun f ↦ Prod.ext
        (ObjectProperty.hom_ext _ (by
          dsimp [F, G, ObjectProperty.lift, Functor.prod, Functor.prod',
            ObjectProperty.isoMk, CategoryTheory.prod.etaIso, Iso.prod]
          simp
          exact (Category.comp_id f.1.hom).trans (Category.id_comp f.1.hom).symm))
        (ObjectProperty.hom_ext _ (by
          dsimp [F, G, ObjectProperty.lift, Functor.prod, Functor.prod',
            ObjectProperty.isoMk, CategoryTheory.prod.etaIso, Iso.prod]
          simp
          exact (Category.comp_id f.2.hom).trans (Category.id_comp f.2.hom).symm))))

end FullSubcategory

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Equivalence

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- Restrict an equivalence into a product category to full subcategories whose object
properties correspond under the equivalence. -/
@[stacks 001K "product object property restricted equivalence"]
def restrictProd (e : C ≌ D × E) {P : ObjectProperty C} {Q : ObjectProperty D}
    {T : ObjectProperty E} [Q.IsClosedUnderIsomorphisms] [T.IsClosedUnderIsomorphisms]
    (h : (Q.prod T).inverseImage e.functor = P) :
    P.FullSubcategory ≌ Q.FullSubcategory × T.FullSubcategory :=
  (e.congrFullSubcategory h).trans (ObjectProperty.FullSubcategory.prodEquivalence Q T)

end CategoryTheory.Equivalence
