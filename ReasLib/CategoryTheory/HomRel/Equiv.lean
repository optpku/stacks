/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.HomRel.Functor
public import ReasLib.CategoryTheory.MorphismProperty.IsPreservedBy

/-!
# Equivalences modulo a relation on morphisms

The canonical morphism property consists of the maps that become isomorphisms in the quotient
category.  For a congruence, this file also packages the equivalent concrete data of a
two-sided inverse modulo the relation.
-/

@[expose] public section

universe u v u' v'

namespace CategoryTheory.HomRel

variable {C : Type u} [Category.{v} C]

/-- An equivalence modulo a relation `r` consists of maps in both directions whose composites
are related to the corresponding identities. -/
@[ext, stacks 019N "equivalence modulo a relation on morphisms"]
structure Equiv (r : HomRel C) (X Y : C) where
  /-- The forward morphism. -/
  hom : X ⟶ Y
  /-- The inverse morphism modulo `r`. -/
  inv : Y ⟶ X
  /-- The forward morphism followed by the inverse is related to the source identity. -/
  hom_inv_id : r (hom ≫ inv) (𝟙 X)
  /-- The inverse followed by the forward morphism is related to the target identity. -/
  inv_hom_id : r (inv ≫ hom) (𝟙 Y)

/-- The morphism property of becoming an isomorphism in the quotient by `r`. -/
@[stacks 019N "morphisms invertible modulo a relation"]
abbrev equivalences (r : HomRel C) : MorphismProperty C :=
  (MorphismProperty.isomorphisms (CategoryTheory.Quotient r)).inverseImage
    (Quotient.functor r)

namespace Equiv

variable {r : HomRel C} {X Y Z : C}
variable {D : Type u'} [Category.{v'} D] {s : HomRel D}

namespace map

/-- Mapping an equivalence along a relation-preserving functor preserves the inverse law at
the source. -/
theorem hom_inv_id (e : Equiv r X Y) (F : C ⥤ D) [IsMappedBy r F s] :
    s (F.map e.hom ≫ F.map e.inv) (𝟙 (F.obj X)) := sorry

/-- Mapping an equivalence along a relation-preserving functor preserves the inverse law at
the target. -/
theorem inv_hom_id (e : Equiv r X Y) (F : C ⥤ D) [IsMappedBy r F s] :
    s (F.map e.inv ≫ F.map e.hom) (𝟙 (F.obj Y)) := sorry

end map

/-- A functor mapping `r` into `s` sends equivalences modulo `r` to equivalences modulo `s`. -/
@[stacks 019N "functoriality of equivalences modulo relations"]
def map (e : Equiv r X Y) (F : C ⥤ D) [IsMappedBy r F s] :
    Equiv s (F.obj X) (F.obj Y) where
  hom := F.map e.hom
  inv := F.map e.inv
  hom_inv_id := map.hom_inv_id e F
  inv_hom_id := map.inv_hom_id e F

namespace map

/-- The forward morphism of a mapped equivalence is the image of its forward morphism. -/
@[simp]
theorem hom (e : Equiv r X Y) (F : C ⥤ D) [IsMappedBy r F s] :
    (e.map (s := s) F).hom = F.map e.hom := sorry

/-- The inverse morphism of a mapped equivalence is the image of its inverse morphism. -/
@[simp]
theorem inv (e : Equiv r X Y) (F : C ⥤ D) [IsMappedBy r F s] :
    (e.map (s := s) F).inv = F.map e.inv := sorry

end map

/-- The images in the quotient of the two maps in an equivalence compose to the source
identity. -/
theorem toIso_hom_inv_id (e : Equiv r X Y) :
    (Quotient.functor r).map e.hom ≫ (Quotient.functor r).map e.inv =
      𝟙 ((Quotient.functor r).obj X) := sorry

/-- The images in the quotient of the two maps in an equivalence compose to the target
identity in the reverse order. -/
theorem toIso_inv_hom_id (e : Equiv r X Y) :
    (Quotient.functor r).map e.inv ≫ (Quotient.functor r).map e.hom =
      𝟙 ((Quotient.functor r).obj Y) := sorry

/-- An equivalence modulo `r` induces an isomorphism in the quotient category. -/
@[stacks 019N "equivalence modulo a relation gives a quotient isomorphism"]
def toIso (e : Equiv r X Y) :
    (Quotient.functor r).obj X ≅ (Quotient.functor r).obj Y where
  hom := (Quotient.functor r).map e.hom
  inv := (Quotient.functor r).map e.inv
  hom_inv_id := toIso_hom_inv_id e
  inv_hom_id := toIso_inv_hom_id e

/-- The forward map of the quotient isomorphism induced by an equivalence. -/
@[simp, stacks 019N "forward map of the quotient isomorphism induced by an equivalence"]
theorem toIso_hom (e : Equiv r X Y) :
    e.toIso.hom = (Quotient.functor r).map e.hom := sorry

/-- The inverse map of the quotient isomorphism induced by an equivalence. -/
@[simp, stacks 019N "inverse map of the quotient isomorphism induced by an equivalence"]
theorem toIso_inv (e : Equiv r X Y) :
    e.toIso.inv = (Quotient.functor r).map e.inv := sorry

/-- The identity is related to itself for a congruence. -/
theorem refl_law (r : HomRel C) [Congruence r] (X : C) :
    r ((𝟙 X) ≫ 𝟙 X) (𝟙 X) := sorry

/-- Every object is equivalent to itself modulo a congruence. -/
@[stacks 019N "reflexivity of equivalence modulo a congruence"]
def refl (r : HomRel C) [Congruence r] (X : C) : Equiv r X X where
  hom := 𝟙 X
  inv := 𝟙 X
  hom_inv_id := refl_law r X
  inv_hom_id := refl_law r X

/-- Reversing the two maps reverses an equivalence modulo a relation. -/
@[stacks 019N "symmetry of equivalence modulo a relation"]
def symm (e : Equiv r X Y) : Equiv r Y X where
  hom := e.inv
  inv := e.hom
  hom_inv_id := e.inv_hom_id
  inv_hom_id := e.hom_inv_id

/-- The proposed composites for transitivity are inverse modulo a congruence at the source. -/
theorem trans_hom_inv_id [Congruence r] (e : Equiv r X Y) (f : Equiv r Y Z) :
    r ((e.hom ≫ f.hom) ≫ (f.inv ≫ e.inv)) (𝟙 X) := sorry

/-- The proposed composites for transitivity are inverse modulo a congruence at the target. -/
theorem trans_inv_hom_id [Congruence r] (e : Equiv r X Y) (f : Equiv r Y Z) :
    r ((f.inv ≫ e.inv) ≫ (e.hom ≫ f.hom)) (𝟙 Z) := sorry

/-- Equivalences modulo a congruence compose. -/
@[stacks 019N "transitivity of equivalence modulo a congruence"]
def trans [Congruence r] (e : Equiv r X Y) (f : Equiv r Y Z) : Equiv r X Z where
  hom := e.hom ≫ f.hom
  inv := f.inv ≫ e.inv
  hom_inv_id := trans_hom_inv_id e f
  inv_hom_id := trans_inv_hom_id e f

/-- The two maps of an isomorphism are inverse modulo a congruence at the source. -/
theorem ofIso_hom_inv_id (r : HomRel C) [Congruence r] (e : X ≅ Y) :
    r (e.hom ≫ e.inv) (𝟙 X) := sorry

/-- The two maps of an isomorphism are inverse modulo a congruence at the target. -/
theorem ofIso_inv_hom_id (r : HomRel C) [Congruence r] (e : X ≅ Y) :
    r (e.inv ≫ e.hom) (𝟙 Y) := sorry

/-- An isomorphism induces an equivalence modulo any congruence. -/
@[stacks 019N "isomorphisms are equivalences modulo a congruence"]
def ofIso (r : HomRel C) [Congruence r] (e : X ≅ Y) : Equiv r X Y where
  hom := e.hom
  inv := e.inv
  hom_inv_id := ofIso_hom_inv_id r e
  inv_hom_id := ofIso_inv_hom_id r e

/-- Representatives of inverse quotient morphisms are inverse modulo the congruence at the
source. -/
theorem ofQuotientIso_hom_inv_id [Congruence r]
    (e : (Quotient.functor r).obj X ≅ (Quotient.functor r).obj Y) :
    r (Quot.out e.hom ≫ Quot.out e.inv) (𝟙 X) := sorry

/-- Representatives of inverse quotient morphisms are inverse modulo the congruence at the
target. -/
theorem ofQuotientIso_inv_hom_id [Congruence r]
    (e : (Quotient.functor r).obj X ≅ (Quotient.functor r).obj Y) :
    r (Quot.out e.inv ≫ Quot.out e.hom) (𝟙 Y) := sorry

/-- An isomorphism between images in the quotient determines an equivalence modulo the
congruence. The representative choices are exposed through the accompanying map lemmas. -/
@[stacks 019N "quotient isomorphism gives an equivalence modulo a congruence"]
noncomputable def ofQuotientIso [Congruence r]
    (e : (Quotient.functor r).obj X ≅ (Quotient.functor r).obj Y) : Equiv r X Y where
  hom := Quot.out e.hom
  inv := Quot.out e.inv
  hom_inv_id := ofQuotientIso_hom_inv_id e
  inv_hom_id := ofQuotientIso_inv_hom_id e

/-- The chosen forward representative maps to the original quotient isomorphism. -/
@[stacks 019N "forward-map specification for a quotient isomorphism representative"]
theorem ofQuotientIso_hom_map [Congruence r]
    (e : (Quotient.functor r).obj X ≅ (Quotient.functor r).obj Y) :
    (Quotient.functor r).map (ofQuotientIso e).hom = e.hom := sorry

/-- The chosen inverse representative maps to the inverse of the original quotient
isomorphism. -/
@[stacks 019N "inverse-map specification for a quotient isomorphism representative"]
theorem ofQuotientIso_inv_map [Congruence r]
    (e : (Quotient.functor r).obj X ≅ (Quotient.functor r).obj Y) :
    (Quotient.functor r).map (ofQuotientIso e).inv = e.inv := sorry

/-- The forward map of an equivalence satisfies the associated morphism property. -/
@[stacks 019N "forward map is invertible modulo the relation"]
theorem mem_equivalences (e : Equiv r X Y) : equivalences r e.hom := sorry

end Equiv

/-- For a congruence, a morphism becomes invertible in the quotient exactly when it is the
forward map of an equivalence modulo the relation. -/
@[stacks 019N "structured criterion for invertibility modulo a relation"]
theorem equivalences_iff (r : HomRel C) [Congruence r] {X Y : C} (f : X ⟶ Y) :
    equivalences r f ↔ ∃ e : Equiv r X Y, e.hom = f := sorry

/-- Two objects are equivalent modulo a congruence exactly when there exists a morphism between
them which becomes invertible in the quotient. -/
@[stacks 019N "object equivalence is existence of an invertible-modulo-relation morphism"]
theorem Equiv.nonempty_iff_exists (r : HomRel C) [Congruence r] {X Y : C} :
    Nonempty (Equiv r X Y) ↔ ∃ f : X ⟶ Y, equivalences r f := sorry

/-- A map satisfies `equivalences r` exactly when its image in the quotient is an isomorphism. -/
@[stacks 019N "isomorphism in a quotient category criterion"]
theorem isIso_quotient_map_iff_equivalences (r : HomRel C) {X Y : C} (f : X ⟶ Y) :
    IsIso ((Quotient.functor r).map f) ↔ equivalences r f := sorry

/-- A map is invertible modulo a congruence exactly when it has a two-sided inverse modulo that
congruence. -/
@[stacks 019N "two-sided inverse criterion modulo a congruence"]
theorem equivalences_iff_exists_inverse (r : HomRel C) [Congruence r]
    {X Y : C} (f : X ⟶ Y) :
    equivalences r f ↔
      ∃ g : Y ⟶ X, r (f ≫ g) (𝟙 X) ∧ r (g ≫ f) (𝟙 Y) := sorry

/-- Every isomorphism becomes an isomorphism in the quotient. -/
@[stacks 019N "isomorphisms are invertible modulo a relation"]
theorem equivalences.isomorphisms_le (r : HomRel C) :
    MorphismProperty.isomorphisms C ≤ equivalences r := sorry

/-- A functor mapping one relation into another maps quotient equivalences into quotient
equivalences. -/
@[stacks 019N "relation-preserving functors map quotient equivalences"]
instance equivalences.isMappedBy {D : Type u'} [Category.{v'} D]
    (r : HomRel C) (F : C ⥤ D) (s : HomRel D) [IsMappedBy r F s] :
    MorphismProperty.IsMappedBy (equivalences r) F (equivalences s) := sorry

end CategoryTheory.HomRel
