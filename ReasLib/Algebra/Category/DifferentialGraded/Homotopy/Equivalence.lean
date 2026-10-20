/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopy Equivalences in a Differential Graded Category

This leaf packages mutually inverse closed degree-zero morphisms up to homotopy and
constructs their canonical isomorphism in the differential graded homotopy category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {C : Type v} [D : DifferentialGradedCategory R C]

open scoped DifferentialGradedCategory

/-- Equal closed degree-zero morphisms are homotopic. -/
theorem Homotopic.of_eq {X Y : C} {f g : CompHom X Y} (h : f = g) :
    Homotopic X Y f g := sorry

/-- Homotopic closed morphisms have equal images in the DG homotopy category. -/
theorem Homotopic.inK_eq {X Y : Comp R C} {f g : X ⟶ Y}
    (h : Homotopic X.obj Y.obj f g) : f.inK = g.inK := sorry

/-- Two closed morphisms have equal images in `K` exactly when they are homotopic. -/
@[simp] theorem CompHom.inK_eq_inK_iff {X Y : Comp R C} {f g : X ⟶ Y} :
    f.inK = g.inK ↔ Homotopic X.obj Y.obj f g := sorry

/-- A homotopy equivalence consists of closed degree-zero morphisms in both directions
whose two composites are homotopic to the corresponding identities. -/
structure HomotopyEquiv (X Y : Comp R C) where
  /-- The forward closed degree-zero morphism. -/
  hom : X ⟶ Y
  /-- The backward closed degree-zero morphism. -/
  inv : Y ⟶ X
  /-- The forward map followed by the backward map is homotopic to the identity. -/
  homotopyHomInvId : Homotopic X.obj X.obj (hom ≫ inv) (𝟙 X)
  /-- The backward map followed by the forward map is homotopic to the identity. -/
  homotopyInvHomId : Homotopic Y.obj Y.obj (inv ≫ hom) (𝟙 Y)

/-- A homotopy retract is a homotopy equivalence whose inverse is a strict section of the
forward map. -/
@[stacks 09QM "homotopy retract"]
structure HomotopyRetract (X Y : Comp R C) where
  /-- The projection onto the retract. -/
  projection : X ⟶ Y
  /-- A strict section of the projection. -/
  section_ : Y ⟶ X
  /-- The section followed by the projection is the identity. -/
  section_projection : section_ ≫ projection = 𝟙 Y
  /-- The projection followed by the section is homotopic to the identity. -/
  projection_section_homotopic :
    Homotopic X.obj X.obj (projection ≫ section_) (𝟙 X)

namespace HomotopyRetract

/-- A homotopy retract determines a homotopy equivalence. -/
def toHomotopyEquiv {X Y : Comp R C} (r : HomotopyRetract X Y) : HomotopyEquiv X Y where
  hom := r.projection
  inv := r.section_
  homotopyHomInvId := r.projection_section_homotopic
  homotopyInvHomId := sorry

/-- The projection of a homotopy retract is split epic. -/
instance isSplitEpi_projection {X Y : Comp R C} (r : HomotopyRetract X Y) :
    IsSplitEpi r.projection :=
  IsSplitEpi.mk' ⟨r.section_, r.section_projection⟩

/-- The section of a homotopy retract is split monic. -/
instance isSplitMono_section {X Y : Comp R C} (r : HomotopyRetract X Y) :
    IsSplitMono r.section_ :=
  IsSplitMono.mk' ⟨r.projection, r.section_projection⟩

/-- The projection of a homotopy retract becomes invertible in the homotopy category. -/
theorem homotopyEquivalences_projection {X Y : Comp R C} (r : HomotopyRetract X Y) :
    Comp.homotopyEquivalences r.projection := sorry

end HomotopyRetract

namespace HomotopyEquiv

/-- The identity closed morphism gives the reflexive homotopy equivalence. -/
@[refl]
def refl (X : Comp R C) : HomotopyEquiv X X where
  hom := 𝟙 X
  inv := 𝟙 X
  homotopyHomInvId := Homotopic.of_eq (Category.comp_id (𝟙 X))
  homotopyInvHomId := Homotopic.of_eq (Category.comp_id (𝟙 X))

/-- Reversing the two maps reverses a homotopy equivalence. -/
@[symm]
def symm {X Y : Comp R C} (e : HomotopyEquiv X Y) : HomotopyEquiv Y X where
  hom := e.inv
  inv := e.hom
  homotopyHomInvId := e.homotopyInvHomId
  homotopyInvHomId := e.homotopyHomInvId

/-- The composite maps underlying the transitive composite are homotopy inverse on the source. -/
theorem trans_hom_inv_id {X Y Z : Comp R C} (e : HomotopyEquiv X Y)
    (e' : HomotopyEquiv Y Z) :
    Homotopic X.obj X.obj
      ((e.hom ≫ e'.hom) ≫ (e'.inv ≫ e.inv)) (𝟙 X) := sorry

/-- The composite maps underlying the transitive composite are homotopy inverse on the target. -/
theorem trans_inv_hom_id {X Y Z : Comp R C} (e : HomotopyEquiv X Y)
    (e' : HomotopyEquiv Y Z) :
    Homotopic Z.obj Z.obj
      ((e'.inv ≫ e.inv) ≫ (e.hom ≫ e'.hom)) (𝟙 Z) := sorry

/-- Homotopy equivalences compose. -/
@[trans]
def trans {X Y Z : Comp R C} (e : HomotopyEquiv X Y)
    (e' : HomotopyEquiv Y Z) : HomotopyEquiv X Z where
  hom := e.hom ≫ e'.hom
  inv := e'.inv ≫ e.inv
  homotopyHomInvId := trans_hom_inv_id e e'
  homotopyInvHomId := trans_inv_hom_id e e'

/-- An isomorphism of closed degree-zero morphisms is a homotopy equivalence. -/
def ofIso {X Y : Comp R C} (e : X ≅ Y) : HomotopyEquiv X Y where
  hom := e.hom
  inv := e.inv
  homotopyHomInvId := Homotopic.of_eq e.hom_inv_id
  homotopyInvHomId := Homotopic.of_eq e.inv_hom_id

/-- The images in `K` of the two maps of a homotopy equivalence compose to the source identity. -/
theorem inK_hom_inv_id {X Y : Comp R C} (e : HomotopyEquiv X Y) :
    e.hom.inK ≫ e.inv.inK = 𝟙 X.inK := sorry

/-- The images in `K` of the two maps of a homotopy equivalence compose to the target identity. -/
theorem inK_inv_hom_id {X Y : Comp R C} (e : HomotopyEquiv X Y) :
    e.inv.inK ≫ e.hom.inK = 𝟙 Y.inK := sorry

/-- A homotopy equivalence induces an explicit isomorphism in the DG homotopy category. -/
def toIso {X Y : Comp R C} (e : HomotopyEquiv X Y) : X.inK ≅ Y.inK where
  hom := e.hom.inK
  inv := e.inv.inK
  hom_inv_id := e.inK_hom_inv_id
  inv_hom_id := e.inK_inv_hom_id

/-- The forward map of `toIso` is the homotopy class of the forward closed morphism. -/
@[simp] theorem toIso_hom {X Y : Comp R C} (e : HomotopyEquiv X Y) :
    e.toIso.hom = e.hom.inK := sorry

/-- The inverse map of `toIso` is the homotopy class of the backward closed morphism. -/
@[simp] theorem toIso_inv {X Y : Comp R C} (e : HomotopyEquiv X Y) :
    e.toIso.inv = e.inv.inK := sorry

/-- The isomorphism induced by the reflexive homotopy equivalence is the identity isomorphism. -/
@[simp] theorem toIso_refl (X : Comp R C) :
    (refl X).toIso = Iso.refl X.inK := sorry

/-- Passing a reversed homotopy equivalence to `K` reverses its induced isomorphism. -/
@[simp] theorem toIso_symm {X Y : Comp R C} (e : HomotopyEquiv X Y) :
    e.symm.toIso = e.toIso.symm := sorry

/-- Passing a composite homotopy equivalence to `K` composes its induced isomorphisms. -/
theorem toIso_trans {X Y Z : Comp R C} (e : HomotopyEquiv X Y)
    (e' : HomotopyEquiv Y Z) :
    (e.trans e').toIso = e.toIso.trans e'.toIso := sorry

/-- The isomorphism in `K` induced from an isomorphism in `Comp` is its functorial image. -/
@[simp] theorem toIso_ofIso {X Y : Comp R C} (e : X ≅ Y) :
    (ofIso e).toIso = Comp.inKFunctor.mapIso e := sorry

end HomotopyEquiv

namespace Comp

/-- A closed degree-zero morphism becomes invertible in `K` exactly when it is the forward
map of a homotopy equivalence. -/
theorem homotopyEquivalences_iff {X Y : Comp R C} (f : X ⟶ Y) :
    homotopyEquivalences f ↔ ∃ e : HomotopyEquiv X Y, e.hom = f := sorry

end Comp

end DifferentialGradedCategory
