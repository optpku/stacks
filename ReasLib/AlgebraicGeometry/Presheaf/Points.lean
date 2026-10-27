/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldValuedPoint

/-!
# Points of presheaves on schemes

Field-valued sections are identified when their restrictions agree over a common
extension field. The presheaf value universe is independent of the base universe.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry.SpacePresheaf

variable {S : Scheme.{u}}

/-- A field-valued point of a presheaf is a field-valued point of the base together
with a section over its spectrum. -/
structure FieldValuedPoint (F : (Over S)ᵒᵖ ⥤ Type v) where
  /-- The field spectrum and its structure morphism to the base. -/
  basePoint : Scheme.FieldValuedPoint S
  /-- The section over the field spectrum. -/
  value : F.obj (op basePoint.over)

namespace FieldValuedPoint

/-- Construct a field-valued section from a field, a structure morphism, and a section. -/
def of {F : (Over S)ᵒᵖ ⥤ Type v} (K : Type u) [Field K]
    (structureHom : Spec (.of K) ⟶ S)
    (value : F.obj (op (Over.mk structureHom))) : FieldValuedPoint F where
  basePoint := Scheme.FieldValuedPoint.of K structureHom
  value := value

/-- Apply a natural transformation to a field-valued section. -/
def map {F G : (Over S)ᵒᵖ ⥤ Type v} (p : FieldValuedPoint F) (f : F ⟶ G) :
    FieldValuedPoint G where
  basePoint := p.basePoint
  value := f.app (op p.basePoint.over) p.value

/-- Two field-valued sections are equivalent when they agree after restriction
to a common extension field over the base. -/
def Equivalent {F : (Over S)ᵒᵖ ⥤ Type v} (p q : FieldValuedPoint F) : Prop :=
  ∃ (r : Scheme.FieldValuedPoint S) (i : r ⟶ p.basePoint) (j : r ⟶ q.basePoint),
    F.map ((Scheme.FieldValuedPoint.toOver S).map i).op p.value =
      F.map ((Scheme.FieldValuedPoint.toOver S).map j).op q.value

/-- Every field-valued section is equivalent to itself. -/
theorem Equivalent.refl {F : (Over S)ᵒᵖ ⥤ Type v} (p : FieldValuedPoint F) :
    Equivalent p p := sorry

/-- Natural transformations preserve common-extension equivalence. -/
theorem Equivalent.map {F G : (Over S)ᵒᵖ ⥤ Type v} {p q : FieldValuedPoint F}
    (h : Equivalent p q) (f : F ⟶ G) : Equivalent (p.map f) (q.map f) := sorry

/-- Field-valued sections form a setoid under common-extension equivalence. -/
def equivalentSetoid (F : (Over S)ᵒᵖ ⥤ Type v) : Setoid (FieldValuedPoint F) where
  r := Equivalent
  iseqv := sorry

/-- The setoid relation is equality after restriction to a common extension field. -/
theorem equivalentSetoid_rel_iff {F : (Over S)ᵒᵖ ⥤ Type v}
    (p q : FieldValuedPoint F) : equivalentSetoid F p q ↔ Equivalent p q := sorry

end FieldValuedPoint

/-- The points of a presheaf are common-extension equivalence classes of
field-valued sections. -/
def Points (F : (Over S)ᵒᵖ ⥤ Type v) :=
  Quotient (FieldValuedPoint.equivalentSetoid F)

namespace Points

/-- The point represented by a field-valued section. -/
def mk {F : (Over S)ᵒᵖ ⥤ Type v} (p : FieldValuedPoint F) : Points F :=
  Quotient.mk (FieldValuedPoint.equivalentSetoid F) p

/-- Two representatives give the same point exactly when they agree over a
common extension field. -/
theorem mk_eq_mk_iff {F : (Over S)ᵒᵖ ⥤ Type v} (p q : FieldValuedPoint F) :
    mk p = mk q ↔ FieldValuedPoint.Equivalent p q := sorry

/-- A natural transformation induces a map on points. -/
def map {F G : (Over S)ᵒᵖ ⥤ Type v} (f : F ⟶ G) : Points F → Points G :=
  Quotient.map (fun p ↦ p.map f) fun _ _ h ↦ FieldValuedPoint.Equivalent.map h f

/-- The induced map on points applies the natural transformation to a representative. -/
theorem map_mk {F G : (Over S)ᵒᵖ ⥤ Type v} (f : F ⟶ G) (p : FieldValuedPoint F) :
    map f (mk p) = mk (p.map f) := sorry

end Points

end AlgebraicGeometry.SpacePresheaf
