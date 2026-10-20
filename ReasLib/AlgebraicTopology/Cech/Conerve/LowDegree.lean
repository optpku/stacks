/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicTopology.Cech.Conerve.Coprojection

/-!
@stack 016N

# Low degrees of a Cech conerve

The degree-zero term of a Cech conerve is canonically isomorphic to the target of the arrow,
while its degree-one term is a pushout of the arrow along itself.  The colimit cocone is exposed
without requiring a separately chosen binary pushout; a comparison with mathlib's chosen
`pushout` is provided only when that choice is already available.
-/

@[expose] public section

open CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C]

namespace cechConerve.degreeZero

variable (f : Arrow C) [f.HasCechConerve]

/-- The identity family satisfies the compatibility condition defining degree zero of the Cech
conerve. -/
@[stacks 016N "degree-zero Cech-conerve inverse compatibility"]
theorem inv_condition :
    forall _ : Fin 1, f.hom ≫ (𝟙 f.right : f.right ⟶ f.right) = f.hom := sorry

/-- The canonical map from degree zero of a Cech conerve to the target of its arrow. -/
@[stacks 016N "degree-zero Cech-conerve inverse"]
noncomputable def inv : f.cechConerve.obj ⦋0⦌ ⟶ f.right :=
  cechConerve.desc f ⦋0⦌ f.hom (fun _ ↦ 𝟙 f.right) (inv_condition f)

/-- The degree-zero coprojection followed by the canonical inverse is the identity. -/
@[reassoc (attr := simp), stacks 016N "degree-zero Cech-conerve coprojection-inverse identity"]
theorem inclusion_comp_inv : cechConerve.ι f ⦋0⦌ 0 ≫ inv f = 𝟙 f.right := sorry

/-- The canonical inverse followed by the degree-zero coprojection is the identity. -/
@[reassoc (attr := simp), stacks 016N "degree-zero Cech-conerve inverse-coprojection identity"]
theorem inv_ι :
    inv f ≫ cechConerve.ι f ⦋0⦌ 0 = 𝟙 (f.cechConerve.obj ⦋0⦌) := sorry

/-- The degree-zero head map has the expected composite with the canonical inverse. -/
@[reassoc (attr := simp), stacks 016N "degree-zero Cech-conerve head inverse computation"]
theorem head_inv : cechConerve.head f ⦋0⦌ ≫ inv f = f.hom := sorry

/-- The canonical identification of the arrow target with degree zero of its Cech conerve. -/
@[stacks 016N "degree-zero Cech-conerve identification"]
noncomputable def iso : f.right ≅ f.cechConerve.obj ⦋0⦌ where
  hom := cechConerve.ι f ⦋0⦌ 0
  inv := inv f
  hom_inv_id := inclusion_comp_inv f
  inv_hom_id := inv_ι f

/-- The forward map of the degree-zero identification is the unique vertex coprojection. -/
@[simp, stacks 016N "degree-zero Cech-conerve identification forward map"]
theorem iso_hom : (iso f).hom = cechConerve.ι f ⦋0⦌ 0 := sorry

/-- The inverse map of the degree-zero identification is the canonical Cech-conerve descent. -/
@[simp, stacks 016N "degree-zero Cech-conerve identification inverse map"]
theorem iso_inv : (iso f).inv = inv f := sorry

end cechConerve.degreeZero

namespace cechConerve.degreeOne

variable (f : Arrow C) [f.HasCechConerve]

/-- The first coprojection into degree one of a Cech conerve. -/
@[stacks 016N "degree-one Cech-conerve first coprojection"]
noncomputable def inl : f.right ⟶ f.cechConerve.obj ⦋1⦌ :=
  cechConerve.ι f ⦋1⦌ 0

/-- The second coprojection into degree one of a Cech conerve. -/
@[stacks 016N "degree-one Cech-conerve second coprojection"]
noncomputable def inr : f.right ⟶ f.cechConerve.obj ⦋1⦌ :=
  cechConerve.ι f ⦋1⦌ 1

/-- The two degree-one coprojections have equal composites with the underlying arrow. -/
@[reassoc, stacks 016N "degree-one Cech-conerve pushout condition"]
theorem condition : f.hom ≫ inl f = f.hom ≫ inr f := sorry

/-- Two compatible maps from the arrow target define a compatible family indexed by the two
vertices. -/
@[stacks 016N "degree-one Cech-conerve descent compatibility"]
theorem desc_condition {Z : C} (a b : f.right ⟶ Z)
    (w : f.hom ≫ a = f.hom ≫ b) :
    forall i : Fin 2, f.hom ≫ Fin.cases a (fun _ ↦ b) i = f.hom ≫ a := sorry

/-- The pushout-style descent used to assemble the degree-one colimit cocone. -/
@[stacks 016N "degree-one Cech-conerve pushout descent"]
noncomputable def desc {Z : C} (a b : f.right ⟶ Z)
    (w : f.hom ≫ a = f.hom ≫ b) :
    f.cechConerve.obj ⦋1⦌ ⟶ Z :=
  cechConerve.desc f ⦋1⦌ (f.hom ≫ a) (Fin.cases a (fun _ ↦ b))
    (desc_condition f a b w)

/-- The internal degree-one descent has the prescribed value on the first coprojection. -/
@[reassoc (attr := simp), stacks 016N "degree-one Cech-conerve descent first coprojection"]
theorem inl_desc {Z : C} (a b : f.right ⟶ Z)
    (w : f.hom ≫ a = f.hom ≫ b) :
    inl f ≫ desc f a b w = a := sorry

/-- The internal degree-one descent has the prescribed value on the second coprojection. -/
@[reassoc (attr := simp), stacks 016N "degree-one Cech-conerve descent second coprojection"]
theorem inr_desc {Z : C} (a b : f.right ⟶ Z)
    (w : f.hom ≫ a = f.hom ≫ b) :
    inr f ≫ desc f a b w = b := sorry

/-- The internal degree-one descent is unique among maps with the prescribed values. -/
@[stacks 016N "degree-one Cech-conerve descent uniqueness"]
theorem desc_unique {Z : C} (a b : f.right ⟶ Z)
    (w : f.hom ≫ a = f.hom ≫ b)
    (m : f.cechConerve.obj ⦋1⦌ ⟶ Z)
    (hinl : inl f ≫ m = a) (hinr : inr f ≫ m = b) :
    m = desc f a b w := sorry

/-- Degree one of a Cech conerve, equipped with its two coprojections, as a pushout cocone. -/
@[stacks 016N "degree-one Cech-conerve pushout cocone"]
noncomputable def cocone : PushoutCocone f.hom f.hom :=
  PushoutCocone.mk (inl f) (inr f) (condition f)

/-- The point of the degree-one pushout cocone is degree one of the Cech conerve. -/
@[simp, stacks 016N "degree-one Cech-conerve pushout cocone point"]
theorem cocone_pt : (cocone f).pt = f.cechConerve.obj ⦋1⦌ := sorry

/-- The first leg of the degree-one pushout cocone is the first vertex coprojection. -/
@[simp, stacks 016N "degree-one Cech-conerve pushout cocone first leg"]
theorem cocone_inl : (cocone f).inl = inl f := sorry

/-- The second leg of the degree-one pushout cocone is the second vertex coprojection. -/
@[simp, stacks 016N "degree-one Cech-conerve pushout cocone second leg"]
theorem cocone_inr : (cocone f).inr = inr f := sorry

/-- Degree one of a Cech conerve is a pushout of the underlying arrow along itself. -/
@[stacks 016N "degree-one Cech-conerve pushout universal property"]
noncomputable def isColimit : IsColimit (cocone f) :=
  PushoutCocone.IsColimit.mk (condition f)
    (fun s ↦ desc f s.inl s.inr s.condition)
    (fun s ↦ inl_desc f s.inl s.inr s.condition)
    (fun s ↦ inr_desc f s.inl s.inr s.condition)
    (fun s m hinl hinr ↦ desc_unique f s.inl s.inr s.condition m hinl hinr)

/-- The comparison from mathlib's chosen pushout to degree one of a Cech conerve. -/
@[stacks 016N "degree-one Cech-conerve chosen-pushout comparison"]
noncomputable def pushoutIso [HasPushout f.hom f.hom] :
    pushout f.hom f.hom ≅ f.cechConerve.obj ⦋1⦌ :=
  (pushoutIsPushout f.hom f.hom).coconePointUniqueUpToIso (isColimit f)

namespace pushoutIso

variable [HasPushout f.hom f.hom]

/-- The chosen-pushout comparison preserves the first coprojection. -/
@[reassoc (attr := simp), stacks 016N "degree-one Cech-conerve comparison first coprojection"]
theorem inl_hom :
    pushout.inl f.hom f.hom ≫ (pushoutIso f).hom = inl f := sorry

/-- The chosen-pushout comparison preserves the second coprojection. -/
@[reassoc (attr := simp), stacks 016N "degree-one Cech-conerve comparison second coprojection"]
theorem inr_hom :
    pushout.inr f.hom f.hom ≫ (pushoutIso f).hom = inr f := sorry

/-- The inverse chosen-pushout comparison preserves the first coprojection. -/
@[reassoc (attr := simp),
  stacks 016N "degree-one Cech-conerve inverse comparison first coprojection"]
theorem inl_inv :
    inl f ≫ (pushoutIso f).inv = pushout.inl f.hom f.hom := sorry

/-- The inverse chosen-pushout comparison preserves the second coprojection. -/
@[reassoc (attr := simp),
  stacks 016N "degree-one Cech-conerve inverse comparison second coprojection"]
theorem inr_inv :
    inr f ≫ (pushoutIso f).inv = pushout.inr f.hom f.hom := sorry

end pushoutIso

/-- The zeroth coface is the second coprojection after identifying the arrow target with degree
zero. -/
@[reassoc (attr := simp), stacks 016N "degree-one Cech-conerve zeroth coface"]
theorem iso_hom_face_zero :
    (cechConerve.degreeZero.iso f).hom ≫ f.cechConerve.δ (0 : Fin 2) = inr f := sorry

/-- The first coface is the first coprojection after identifying the arrow target with degree
zero. -/
@[reassoc (attr := simp), stacks 016N "degree-one Cech-conerve first coface"]
theorem iso_hom_face_one :
    (cechConerve.degreeZero.iso f).hom ≫ f.cechConerve.δ (1 : Fin 2) = inl f := sorry

/-- The inverse degree-zero identification followed by the second coprojection recovers the
zeroth coface. -/
@[reassoc (attr := simp), stacks 016N "degree-one Cech-conerve zeroth coface inverse formula"]
theorem iso_inv_inr :
    (cechConerve.degreeZero.iso f).inv ≫ inr f =
      f.cechConerve.δ (0 : Fin 2) := sorry

/-- The inverse degree-zero identification followed by the first coprojection recovers the first
coface. -/
@[reassoc (attr := simp), stacks 016N "degree-one Cech-conerve first coface inverse formula"]
theorem iso_inv_inl :
    (cechConerve.degreeZero.iso f).inv ≫ inl f =
      f.cechConerve.δ (1 : Fin 2) := sorry

/-- The degree-zero codegeneracy, transported to the arrow target, is the codiagonal from degree
one. -/
@[stacks 016N "degree-one Cech-conerve codiagonal"]
noncomputable def codiagonal : f.cechConerve.obj ⦋1⦌ ⟶ f.right :=
  f.cechConerve.σ (0 : Fin 1) ≫ (cechConerve.degreeZero.iso f).inv

/-- The codiagonal from degree one is the identity on the first component. -/
@[reassoc (attr := simp), stacks 016N "degree-one Cech-conerve codiagonal first component"]
theorem inl_codiagonal : inl f ≫ codiagonal f = 𝟙 f.right := sorry

/-- The codiagonal from degree one is the identity on the second component. -/
@[reassoc (attr := simp), stacks 016N "degree-one Cech-conerve codiagonal second component"]
theorem inr_codiagonal : inr f ≫ codiagonal f = 𝟙 f.right := sorry

end cechConerve.degreeOne

end CategoryTheory.Arrow
