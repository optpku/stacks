/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived.Explicit

@[expose] public section

/-!
# Canonical First Derived Limits

This file specializes the explicit-cone Milnor cokernel construction to the product cone selected
by `HasProduct` and packages the resulting canonical construction as a functor.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.SequentialInverseSystem.Milnor.ProductCone

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Canonical

variable [HasCokernels C]

/-- The canonical Milnor cokernel formed from the product selected by `HasProduct`. -/
@[stacks 08TC]
abbrev canonicalR1 (K : SequentialInverseSystem C) [HasProduct K.family] : C :=
  cokernel K.milnorDifferenceMap

namespace canonicalR1

/-- The canonical quotient from the selected product to `canonicalR1`. -/
abbrev π (K : SequentialInverseSystem C) [HasProduct K.family] :
    ∏ᶜ K.family ⟶ canonicalR1 K :=
  cokernel.π K.milnorDifferenceMap

/-- The morphism out of `canonicalR1` induced by a morphism from the product that annihilates
the Milnor difference map. -/
@[stacks 08TC]
abbrev desc (K : SequentialInverseSystem C) [HasProduct K.family] {Z : C}
    (f : ∏ᶜ K.family ⟶ Z) (h : K.milnorDifferenceMap ≫ f = 0) :
    canonicalR1 K ⟶ Z :=
  cokernel.desc K.milnorDifferenceMap f h

/-- The morphism `desc K f h` factors `f` through the canonical Milnor quotient. -/
@[reassoc (attr := simp)]
theorem π_desc (K : SequentialInverseSystem C) [HasProduct K.family] {Z : C}
    (f : ∏ᶜ K.family ⟶ Z) (h : K.milnorDifferenceMap ≫ f = 0) :
    π K ≫ desc K f h = f := sorry

/-- A morphism out of `canonicalR1` is determined by its composite with the canonical Milnor
quotient. -/
theorem desc_uniq (K : SequentialInverseSystem C) [HasProduct K.family] {Z : C}
    (f : ∏ᶜ K.family ⟶ Z) (h : K.milnorDifferenceMap ≫ f = 0)
    (g : canonicalR1 K ⟶ Z) (hg : π K ≫ g = f) :
    g = desc K f h := sorry

/-- The canonical map on Milnor cokernels induced by a morphism of sequential inverse systems. -/
@[stacks 08TC]
abbrev map {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (f : K ⟶ L) :
    canonicalR1 K ⟶ canonicalR1 L :=
  cokernel.map K.milnorDifferenceMap L.milnorDifferenceMap
    (SequentialInverseSystem.productMap f) (SequentialInverseSystem.productMap f)
    (SequentialInverseSystem.milnorDifferenceMap_naturality f)

/-- The selected-product presentation of `canonicalR1` agrees at the object level with the
usual cokernel of `milnorDifferenceMap`. -/
theorem eq_cokernel (K : SequentialInverseSystem C) [HasProduct K.family] :
    canonicalR1 K = cokernel K.milnorDifferenceMap := sorry

/-- The explicit-cone construction on the selected product cone agrees with the canonical
Milnor cokernel model. -/
theorem explicit_eq (K : SequentialInverseSystem C) [HasProduct K.family] :
    R1 K (getLimitCone (Discrete.functor K.family)) = canonicalR1 K := sorry

/-- Canonical Milnor quotients are natural with respect to the usual product map. -/
@[reassoc, stacks 08TC]
theorem π_map {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (f : K ⟶ L) :
    π K ≫ map f = SequentialInverseSystem.productMap f ≫ π L := sorry

/-- The canonical map associated to an identity morphism is the identity. -/
@[simp]
theorem map_id (K : SequentialInverseSystem C) [HasProduct K.family] :
    map (𝟙 K) = 𝟙 (canonicalR1 K) := sorry

/-- Canonical maps on Milnor cokernels preserve composition. -/
@[simp]
theorem map_comp {K L M : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] [HasProduct M.family]
    (f : K ⟶ L) (g : L ⟶ M) :
    map (f ≫ g) = map f ≫ map g := sorry

/-- The canonical Milnor cokernel maps induced by the two directions of a tower isomorphism
compose to the identity on the source. -/
theorem map_hom_inv_id {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (e : K ≅ L) :
    map e.hom ≫ map e.inv = 𝟙 (canonicalR1 K) := sorry

/-- The canonical Milnor cokernel maps induced by the two directions of a tower isomorphism
compose to the identity on the target. -/
theorem map_inv_hom_id {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (e : K ≅ L) :
    map e.inv ≫ map e.hom = 𝟙 (canonicalR1 L) := sorry

/-- The isomorphism of canonical Milnor cokernels induced by an isomorphism of sequential
inverse systems. Its morphisms are the corresponding canonical cokernel maps. -/
@[stacks 08TC]
def mapIso {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (e : K ≅ L) :
    canonicalR1 K ≅ canonicalR1 L where
  hom := map e.hom
  inv := map e.inv
  hom_inv_id := map_hom_inv_id e
  inv_hom_id := map_inv_hom_id e

/-- The forward morphism of `mapIso` is the canonical Milnor cokernel map induced by
`e.hom`. -/
@[simp]
theorem mapIso_hom {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (e : K ≅ L) :
    (mapIso e).hom = map e.hom := sorry

/-- The inverse morphism of `mapIso` is the canonical Milnor cokernel map induced by
`e.inv`. -/
@[simp]
theorem mapIso_inv {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (e : K ≅ L) :
    (mapIso e).inv = map e.inv := sorry

/-- Canonical Milnor cokernel maps preserve isomorphisms of sequential inverse systems. -/
@[stacks 08TC]
instance mapIsIso {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family]
    (f : K ⟶ L) [IsIso f] : IsIso (map f) := sorry

section Functor

variable [HasCountableProducts C]

/-- The canonical first-derived-limit functor obtained from selected countable products and
their Milnor cokernels. -/
@[stacks 08TC]
def functor : SequentialInverseSystem C ⥤ C where
  obj K := canonicalR1 (C := C) K
  map f := canonicalR1.map (C := C) f
  map_id K := canonicalR1.map_id (C := C) K
  map_comp f g := canonicalR1.map_comp (C := C) f g

/-- The canonical first-derived-limit functor evaluates to `canonicalR1` on objects. -/
@[simp]
theorem functor_obj (K : SequentialInverseSystem C) :
    (functor (C := C)).obj K = canonicalR1 K := sorry

/-- The canonical first-derived-limit functor uses the canonical Milnor cokernel map on
morphisms. -/
@[simp]
theorem functor_map {K L : SequentialInverseSystem C} (f : K ⟶ L) :
    (functor (C := C)).map f = canonicalR1.map f := sorry

end Functor

end canonicalR1

end Canonical

end CategoryTheory.SequentialInverseSystem.Milnor.ProductCone
