/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient.Conormal

/-!
# Isomorphism classes of invertible quotients

This file identifies invertible quotients when their targets are compatibly
isomorphic. It also provides the uniquely determined target isomorphism
between two representatives of one class.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.InvertibleQuotient

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Two invertible quotients are related when an isomorphism of their targets
commutes with their quotient morphisms. -/
def Rel {E : C} (q q' : InvertibleQuotient E) : Prop :=
  ∃ e : q.object ≅ q'.object, q.hom ≫ e.hom = q'.hom

/-- Compatible target isomorphism is an equivalence relation on invertible quotients. -/
theorem rel_isEquivalence (E : C) : _root_.Equivalence (@Rel C _ _ E) := sorry

/-- The setoid of invertible quotients modulo compatible target isomorphism. -/
def setoid (E : C) : Setoid (InvertibleQuotient E) :=
  ⟨Rel, rel_isEquivalence E⟩

/-- An isomorphism class of epimorphic quotients onto invertible objects. -/
def IsoClass (E : C) : Type (max u v) := Quotient (setoid E)

namespace IsoClass

/-- The isomorphism class represented by an invertible quotient. -/
def mk {E : C} (q : InvertibleQuotient E) : IsoClass E :=
  Quotient.mk (setoid E) q

end IsoClass

/-- Two representatives determine the same quotient class exactly when their targets are
compatibly isomorphic. -/
theorem isoClass_eq_iff {E : C} (q q' : InvertibleQuotient E) :
    IsoClass.mk q = IsoClass.mk q' ↔ Rel q q' := sorry

/-- The target isomorphism canonically forced by equality of two quotient classes. -/
noncomputable def targetIsoOfMkEq {E : C} {q q' : InvertibleQuotient E}
    (h : IsoClass.mk q = IsoClass.mk q') : q.object ≅ q'.object :=
  Classical.choose (Quotient.exact h)

/-- The target isomorphism attached to equality of quotient classes commutes with the
quotient morphisms. -/
theorem targetIsoOfMkEq_spec {E : C} {q q' : InvertibleQuotient E}
    (h : IsoClass.mk q = IsoClass.mk q') :
    q.hom ≫ (targetIsoOfMkEq h).hom = q'.hom := sorry

/-- A compatible target isomorphism between representatives of one quotient class is unique. -/
theorem targetIsoOfMkEq_unique {E : C} {q q' : InvertibleQuotient E}
    (h : IsoClass.mk q = IsoClass.mk q') (e : q.object ≅ q'.object)
    (he : q.hom ≫ e.hom = q'.hom) :
    e = targetIsoOfMkEq h := sorry

/-- The canonical target isomorphism attached to reflexive equality is the identity. -/
theorem targetIsoOfMkEq_refl {E : C} (q : InvertibleQuotient E) :
    targetIsoOfMkEq (q := q) (q' := q) rfl = Iso.refl q.object := sorry

/-- Source transport preserves compatible target isomorphism. -/
theorem precomposeIso_rel {E E' : C} (e : E ≅ E')
    {q q' : InvertibleQuotient E'} (h : Rel q q') :
    Rel (precomposeIso e q) (precomposeIso e q') := sorry

/-- Source transport induces a map on isomorphism classes of invertible quotients. -/
def precomposeIsoClass {E E' : C} (e : E ≅ E') : IsoClass E' → IsoClass E :=
  Quotient.map (precomposeIso e) (fun _ _ ↦ precomposeIso_rel e)

/-- Transporting quotient classes along an isomorphism and its inverse is the identity. -/
theorem precomposeIsoClass_symm_apply {E E' : C} (e : E ≅ E')
    (q : IsoClass E') :
    precomposeIsoClass e.symm (precomposeIsoClass e q) = q := sorry

/-- Isomorphic source objects have equivalent types of invertible-quotient classes. -/
def isoClassEquivOfIso {E E' : C} (e : E ≅ E') : IsoClass E ≃ IsoClass E' where
  toFun := precomposeIsoClass e.symm
  invFun := precomposeIsoClass e
  left_inv := precomposeIsoClass_symm_apply e.symm
  right_inv := precomposeIsoClass_symm_apply e

end CategoryTheory.InvertibleQuotient
