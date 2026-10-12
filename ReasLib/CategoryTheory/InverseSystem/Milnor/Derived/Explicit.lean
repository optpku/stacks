/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Milnor.ProductCone
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# First Derived Limits on Explicit Product Cones

This file gives the Milnor cokernel construction independently of derived categories, retaining
an explicitly supplied product `LimitCone`. Consequently constructions with chosen products do
not acquire a global countable-product assumption merely to form their first derived limit.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.SequentialInverseSystem.Milnor.ProductCone

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The first derived inverse limit presented as the cokernel of the Milnor
difference on an explicitly supplied product cone. -/
@[stacks 08TC]
abbrev R1 (K : SequentialInverseSystem C)
    (P : LimitCone (Discrete.functor K.family))
    [HasCokernel (difference K P)] : C :=
  cokernel (difference K P)

namespace R1

/-- The quotient from an explicitly supplied product cone to its Milnor cokernel. -/
abbrev π (K : SequentialInverseSystem C)
    (P : LimitCone (Discrete.functor K.family))
    [HasCokernel (difference K P)] : P.cone.pt ⟶ R1 K P :=
  cokernel.π (difference K P)

/-- The map on explicit-cone Milnor cokernels induced by a morphism of sequential inverse
systems. -/
@[stacks 08TC]
def map {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family))
    [HasCokernel (difference K P)] [HasCokernel (difference L Q)]
    (f : K ⟶ L) : R1 K P ⟶ R1 L Q :=
  cokernel.map (difference K P) (difference L Q)
    (ProductCone.map P Q f) (ProductCone.map P Q f)
    (ProductCone.difference_naturality P Q f)

/-- Quotients to explicit-cone Milnor cokernels are natural in the sequential inverse system. -/
@[reassoc, stacks 08TC]
theorem π_map {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family))
    [HasCokernel (difference K P)] [HasCokernel (difference L Q)]
    (f : K ⟶ L) :
    π K P ≫ map P Q f = ProductCone.map P Q f ≫ π L Q := sorry

/-- The identity of a sequential inverse system induces the identity of its explicit-cone
Milnor cokernel. -/
@[simp]
theorem map_id (K : SequentialInverseSystem C)
    (P : LimitCone (Discrete.functor K.family))
    [HasCokernel (difference K P)] :
    map P P (𝟙 K) = 𝟙 (R1 K P) := sorry

/-- Maps on explicit-cone Milnor cokernels preserve composition. -/
@[simp]
theorem map_comp {K L M : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family))
    (S : LimitCone (Discrete.functor M.family))
    [HasCokernel (difference K P)] [HasCokernel (difference L Q)]
    [HasCokernel (difference M S)] (f : K ⟶ L) (g : L ⟶ M) :
    map P S (f ≫ g) = map P Q f ≫ map Q S g := sorry

/-- The explicit-cone Milnor cokernel maps induced by the two directions of a tower
isomorphism compose to the identity on the source. -/
theorem map_hom_inv_id {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family))
    [HasCokernel (difference K P)] [HasCokernel (difference L Q)] (e : K ≅ L) :
    map P Q e.hom ≫ map Q P e.inv = 𝟙 (R1 K P) := sorry

/-- The explicit-cone Milnor cokernel maps induced by the two directions of a tower
isomorphism compose to the identity on the target. -/
theorem map_inv_hom_id {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family))
    [HasCokernel (difference K P)] [HasCokernel (difference L Q)] (e : K ≅ L) :
    map Q P e.inv ≫ map P Q e.hom = 𝟙 (R1 L Q) := sorry

/-- The isomorphism of explicit-cone Milnor cokernels induced by an isomorphism of sequential
inverse systems. Its morphisms are the corresponding explicit-cone cokernel maps. -/
@[stacks 08TC]
def mapIso {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family))
    [HasCokernel (difference K P)] [HasCokernel (difference L Q)] (e : K ≅ L) :
    R1 K P ≅ R1 L Q where
  hom := map P Q e.hom
  inv := map Q P e.inv
  hom_inv_id := map_hom_inv_id P Q e
  inv_hom_id := map_inv_hom_id P Q e

/-- The forward morphism of `mapIso` is the explicit-cone Milnor cokernel map induced by
`e.hom`. -/
@[simp]
theorem mapIso_hom {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family))
    [HasCokernel (difference K P)] [HasCokernel (difference L Q)] (e : K ≅ L) :
    (mapIso P Q e).hom = map P Q e.hom := sorry

/-- The inverse morphism of `mapIso` is the explicit-cone Milnor cokernel map induced by
`e.inv`. -/
@[simp]
theorem mapIso_inv {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family))
    [HasCokernel (difference K P)] [HasCokernel (difference L Q)] (e : K ≅ L) :
    (mapIso P Q e).inv = map Q P e.inv := sorry

/-- Maps of explicit-cone Milnor cokernels preserve isomorphisms of sequential inverse
systems. -/
@[stacks 08TC]
instance mapIsIso {K L : SequentialInverseSystem C}
    (P : LimitCone (Discrete.functor K.family))
    (Q : LimitCone (Discrete.functor L.family))
    [HasCokernel (difference K P)] [HasCokernel (difference L Q)]
    (f : K ⟶ L) [IsIso f] : IsIso (map P Q f) := sorry

end R1

end CategoryTheory.SequentialInverseSystem.Milnor.ProductCone
