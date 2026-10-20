/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Milnor

@[expose] public section

/-!
# Milnor Maps on Explicit Product Cones

This leaf formulates the Milnor difference map on a supplied product
`LimitCone`, rather than on the product selected by a `HasProduct` instance.
It is the neutral owner used by constructions that must retain their chosen
product and its projections as explicit data.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.SequentialInverseSystem.Milnor.ProductCone

variable {C : Type u} [Category.{v} C]

/-- The `n`th projection of an explicitly supplied product cone. -/
def projection {K : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family)) (n : ℕ) :
    P.cone.pt ⟶ K.obj (op n) :=
  P.cone.π.app ⟨n⟩

/-- On the limit cone selected by a `HasProduct` instance, the explicit-cone projection is the
usual product projection. -/
@[simp]
theorem projection_getLimitCone (K : SequentialInverseSystem C) [HasProduct K.family]
    (n : ℕ) :
    projection (getLimitCone (Discrete.functor K.family)) n = Pi.π K.family n := sorry

section

variable [Preadditive C]

/-- The Milnor difference endomorphism on an explicitly supplied product cone. -/
@[stacks 08TC]
def difference (K : SequentialInverseSystem C)
    (P : LimitCone (Discrete.functor K.family)) : P.cone.pt ⟶ P.cone.pt :=
  P.isLimit.lift <| Fan.mk P.cone.pt fun n ↦
    projection P n - projection P (n + 1) ≫ K.transitionMap (Nat.le_succ n)

/-- The `n`th projection of the explicit-cone Milnor difference is the difference of the
current projection and the successor projection followed by the transition map. -/
@[reassoc (attr := simp)]
theorem difference_comp_projection (K : SequentialInverseSystem C)
    (P : LimitCone (Discrete.functor K.family)) (n : ℕ) :
    difference K P ≫ projection P n =
      projection P n - projection P (n + 1) ≫ K.transitionMap (Nat.le_succ n) := sorry

/-- On the limit cone selected by a `HasProduct` instance, the explicit-cone difference is the
existing Milnor difference map. -/
@[simp]
theorem difference_getLimitCone (K : SequentialInverseSystem C) [HasProduct K.family] :
    difference K (getLimitCone (Discrete.functor K.family)) = K.milnorDifferenceMap := sorry

end

/-- The map between the points of two explicit product cones induced by a morphism of
sequential inverse systems. -/
@[stacks 08TC]
def map {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family)) (f : K ⟶ L) :
    P.cone.pt ⟶ Q.cone.pt :=
  Q.isLimit.lift <| Fan.mk P.cone.pt fun n ↦ projection P n ≫ f.app (op n)

/-- The explicit product-cone map has the expected component at every stage. -/
@[reassoc (attr := simp)]
theorem map_comp_projection {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family)) (f : K ⟶ L) (n : ℕ) :
    map P Q f ≫ projection Q n = projection P n ≫ f.app (op n) := sorry

/-- On product cones selected by `HasProduct` instances, the explicit-cone map is the existing
product map of inverse systems. -/
@[simp]
theorem map_getLimitCone {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (f : K ⟶ L) :
    map (getLimitCone (Discrete.functor K.family))
      (getLimitCone (Discrete.functor L.family)) f = productMap f := sorry

/-- The explicit product-cone map induced by an identity transformation is the identity. -/
@[simp]
theorem map_id {K : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family)) :
    map P P (𝟙 K) = 𝟙 P.cone.pt := sorry

/-- Maps between explicit product cones respect composition of tower morphisms. -/
@[reassoc]
theorem map_comp {K L M : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family))
    (R : LimitCone (Discrete.functor M.family)) (f : K ⟶ L) (g : L ⟶ M) :
    map P Q f ≫ map Q R g = map P R (f ≫ g) := sorry

section

variable [Preadditive C]

/-- The Milnor difference endomorphism is natural for maps between explicitly supplied product
cones. -/
@[reassoc]
theorem difference_naturality {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family)) (f : K ⟶ L) :
    difference K P ≫ map P Q f = map P Q f ≫ difference L Q := sorry

end

/-- The maps induced by the two directions of a tower isomorphism compose to the identity on
the source explicit product cone. -/
theorem map_hom_inv_id {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    map P Q e.hom ≫ map Q P e.inv = 𝟙 P.cone.pt := sorry

/-- The maps induced by the two directions of a tower isomorphism compose to the identity on
the target explicit product cone. -/
theorem map_inv_hom_id {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    map Q P e.inv ≫ map P Q e.hom = 𝟙 Q.cone.pt := sorry

/-- The isomorphism between the points of two explicit product cones induced by an isomorphism
of sequential inverse systems. Its morphisms are the explicit product-cone maps. -/
@[stacks 08TC]
def mapIso {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    P.cone.pt ≅ Q.cone.pt where
  hom := map P Q e.hom
  inv := map Q P e.inv
  hom_inv_id := map_hom_inv_id P Q e
  inv_hom_id := map_inv_hom_id P Q e

/-- The forward morphism of `mapIso` is the explicit product-cone map induced by `e.hom`. -/
@[simp]
theorem mapIso_hom {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    (mapIso P Q e).hom = map P Q e.hom := sorry

/-- The inverse morphism of `mapIso` is the explicit product-cone map induced by `e.inv`. -/
@[simp]
theorem mapIso_inv {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    (mapIso P Q e).inv = map Q P e.inv := sorry

end CategoryTheory.SequentialInverseSystem.Milnor.ProductCone
