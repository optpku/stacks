/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Chow
public import ReasLib.AlgebraicGeometry.Correspondence.Graph

@[expose] public section

open CategoryTheory hiding Category
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- Objects of the category of rational Chow correspondences are smooth projective
schemes over the ground field. -/
def Category (k : Type u) [Field k] :=
  { X : SchemeOverField k // Smooth X.hom ∧ Projective X.hom }

namespace Category

/-- The smooth projective scheme underlying an object of the correspondence category. -/
def scheme {k : Type u} [Field k] (X : Category k) : SchemeOverField k :=
  X.val

/-- The underlying scheme of a correspondence-category object is smooth over the field. -/
instance scheme_smooth {k : Type u} [Field k] (X : Category k) : Smooth X.scheme.hom :=
  X.property.1

/-- The underlying scheme of a correspondence-category object is projective over the field. -/
instance scheme_projective {k : Type u} [Field k] (X : Category k) :
    Projective X.scheme.hom :=
  X.property.2

/-- The underlying scheme of a correspondence-category object is locally of finite type. -/
instance scheme_locallyOfFiniteType {k : Type u} [Field k] (X : Category k) :
    LocallyOfFiniteType X.scheme.hom := sorry

/-- The product of two objects, with underlying scheme their fibre product over `k`. -/
noncomputable def product {k : Type u} [Field k] (X Y : Category k) : Category k :=
  let properties : Smooth (X.scheme ⨯ Y.scheme).hom ∧ Projective (X.scheme ⨯ Y.scheme).hom := sorry
  ⟨X.scheme ⨯ Y.scheme, properties⟩

/-- The scheme underlying `product X Y` is `X.scheme ⨯ Y.scheme`. -/
theorem scheme_product {k : Type u} [Field k] (X Y : Category k) :
    (product X Y).scheme = (X.scheme ⨯ Y.scheme) := sorry

/-- The tensor-unit object, with underlying scheme `Spec(k)`. -/
noncomputable def unit (k : Type u) [Field k] : Category k :=
  let properties : Smooth (SchemeOverField.point k).hom ∧
      Projective (SchemeOverField.point k).hom := sorry
  ⟨SchemeOverField.point k, properties⟩

/-- The scheme underlying the tensor unit is the canonical field point `Spec(k)`. -/
theorem scheme_unit (k : Type u) [Field k] :
    (unit k).scheme = SchemeOverField.point k := sorry

end Category

/-- The rational graph correspondence associated to an isomorphism of smooth projective
schemes, oriented from its source to its target. -/
noncomputable def rationalGraphIso {k : Type u} [Field k] (X Y : Category k)
    (f : X.scheme ≅ Y.scheme) : Rational X.scheme Y.scheme 0 :=
  rationalGraph f.inv

/-- The morphism type between two smooth projective schemes in the correspondence category. -/
abbrev correspondenceHom {k : Type u} [Field k] (X Y : Category k) :=
  Rational X.scheme Y.scheme 0

/-- The identity rational correspondence of a smooth projective scheme. -/
noncomputable def correspondenceId {k : Type u} [Field k] (X : Category k) :
    correspondenceHom X X :=
  rationalGraphIso X X (Iso.refl X.scheme)

/-- Composition of degree-zero rational Chow correspondences. -/
def correspondenceComp {k : Type u} [Field k] {X Y Z : Category k}
    (f : correspondenceHom X Y) (g : correspondenceHom Y Z) : correspondenceHom X Z :=
  composition X.scheme Y.scheme Z.scheme 0 0 f g

set_option backward.privateInPublic true in
/-- The category structure determined by the correspondence operations and their laws. -/
@[implicit_reducible]
private def categoryOfLaws {k : Type u} [Field k]
    (assoc : ∀ {W X Y Z : Category k} (f : correspondenceHom W X)
      (g : correspondenceHom X Y) (h : correspondenceHom Y Z),
      correspondenceComp (correspondenceComp f g) h =
        correspondenceComp f (correspondenceComp g h))
    (id_comp : ∀ {X Y : Category k} (f : correspondenceHom X Y),
      correspondenceComp (correspondenceId X) f = f)
    (comp_id : ∀ {X Y : Category k} (f : correspondenceHom X Y),
      correspondenceComp f (correspondenceId Y) = f) :
    CategoryTheory.Category.{u + 1} (Category k) where
  Hom := correspondenceHom
  id := correspondenceId
  comp := correspondenceComp
  assoc := assoc
  id_comp := id_comp
  comp_id := comp_id

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Degree-zero rational Chow correspondences form a category under pull-intersect-push
composition. -/
instance instCategory {k : Type u} [Field k] :
    CategoryTheory.Category.{u + 1} (Category k) :=
  let laws :
      (∀ {W X Y Z : Category k} (f : correspondenceHom W X)
        (g : correspondenceHom X Y) (h : correspondenceHom Y Z),
        correspondenceComp (correspondenceComp f g) h =
          correspondenceComp f (correspondenceComp g h)) ∧
      (∀ {X Y : Category k} (f : correspondenceHom X Y),
        correspondenceComp (correspondenceId X) f = f) ∧
      (∀ {X Y : Category k} (f : correspondenceHom X Y),
        correspondenceComp f (correspondenceId Y) = f) := sorry
  categoryOfLaws laws.1 laws.2.1 laws.2.2

end AlgebraicGeometry.Correspondence
