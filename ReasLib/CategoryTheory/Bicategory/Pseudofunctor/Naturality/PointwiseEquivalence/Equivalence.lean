/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Constructors
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Inverse

/-!
# Assembled equivalences from pointwise equivalence data

This leaf assembles the mate-defined inverse and supplied component units and
counits into a bicategorical equivalence of pseudofunctors, with direct
readout and round-trip APIs.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {F G : Pseudofunctor B D}

namespace PointwiseEquivalence

variable {η : F ⟶ G}

/-- Naturality of the pointwise units as a modification from the identity transformation to
the forward transformation followed by its inverse. -/
theorem unitIso.naturality
    (h : PointwiseEquivalence η) {a b : B} (f : a ⟶ b) :
    F.map f ◁ (h.unit b).hom ≫
        ((StrongTrans.vcomp η h.inverse).naturality f).hom =
      ((StrongTrans.id F).naturality f).hom ≫
        (h.unit a).hom ▷ F.map f := sorry

/-- The pointwise units assemble into the unit isomorphism of strong transformations. -/
@[stacks 0040 "unit modification of a pointwise equivalence"]
def unitIso (h : PointwiseEquivalence η) :
    StrongTrans.id F ≅ StrongTrans.vcomp η h.inverse :=
  StrongTrans.isoMk
    (η := StrongTrans.id F) (θ := StrongTrans.vcomp η h.inverse)
    h.unit (unitIso.naturality h)

/-- Naturality of the pointwise counits as a modification from the inverse transformation
followed by the forward transformation to the identity. -/
theorem counitIso.naturality
    (h : PointwiseEquivalence η) {a b : B} (f : a ⟶ b) :
    G.map f ◁ (h.counit b).hom ≫
        ((StrongTrans.id G).naturality f).hom =
      ((StrongTrans.vcomp h.inverse η).naturality f).hom ≫
        (h.counit a).hom ▷ G.map f := sorry

/-- The pointwise counits assemble into the counit isomorphism of strong transformations. -/
@[stacks 0040 "counit modification of a pointwise equivalence"]
def counitIso (h : PointwiseEquivalence η) :
    StrongTrans.vcomp h.inverse η ≅ StrongTrans.id G :=
  StrongTrans.isoMk
    (η := StrongTrans.vcomp h.inverse η) (θ := StrongTrans.id G)
    h.counit (counitIso.naturality h)

/-- The forward unit component of the assembled strong-transformation equivalence. -/
@[simp]
theorem unitIso.hom.app (h : PointwiseEquivalence η) (a : B) :
    h.unitIso.hom.as.app a = (h.unit a).hom := sorry

/-- The inverse unit component of the assembled strong-transformation equivalence. -/
@[simp]
theorem unitIso.inv.app (h : PointwiseEquivalence η) (a : B) :
    h.unitIso.inv.as.app a = (h.unit a).inv := sorry

/-- The forward counit component of the assembled strong-transformation equivalence. -/
@[simp]
theorem counitIso.hom.app (h : PointwiseEquivalence η) (a : B) :
    h.counitIso.hom.as.app a = (h.counit a).hom := sorry

/-- The inverse counit component of the assembled strong-transformation equivalence. -/
@[simp]
theorem counitIso.inv.app (h : PointwiseEquivalence η) (a : B) :
    h.counitIso.inv.as.app a = (h.counit a).inv := sorry

/-- The assembled unit and counit satisfy the left triangle identity in the functor
bicategory. -/
theorem toEquivalence.left_triangle
    (h : PointwiseEquivalence η) :
    Bicategory.leftZigzagIso h.unitIso h.counitIso =
      λ_ η ≪≫ (ρ_ η).symm := sorry

/-- A strong transformation equipped with chosen pointwise equivalence data is an equivalence
in the pseudofunctor bicategory. -/
@[stacks 0040 "pseudofunctor equivalence from pointwise equivalence data"]
def toEquivalence (h : PointwiseEquivalence η) : F ≌ G where
  hom := η
  inv := h.inverse
  unit := h.unitIso
  counit := h.counitIso
  left_triangle := toEquivalence.left_triangle h

/-- The forward strong transformation of the assembled equivalence is the original
transformation. -/
@[simp]
theorem toEquivalence.hom (h : PointwiseEquivalence η) :
    h.toEquivalence.hom = η := sorry

/-- The inverse strong transformation of the assembled equivalence is the mate-defined
pointwise inverse. -/
@[simp]
theorem toEquivalence.inv (h : PointwiseEquivalence η) :
    h.toEquivalence.inv = h.inverse := sorry

/-- The unit of the assembled equivalence is `unitIso`. -/
@[simp]
theorem toEquivalence.unit (h : PointwiseEquivalence η) :
    h.toEquivalence.unit = h.unitIso := sorry

/-- The counit of the assembled equivalence is `counitIso`. -/
@[simp]
theorem toEquivalence.counit (h : PointwiseEquivalence η) :
    h.toEquivalence.counit = h.counitIso := sorry

/-- The forward component of the assembled equivalence is the original strong-transformation
component. -/
@[simp]
theorem toEquivalence.hom.app (h : PointwiseEquivalence η) (a : B) :
    h.toEquivalence.hom.app a = η.app a := sorry

/-- The inverse component of the assembled equivalence is the chosen pointwise inverse. -/
@[simp]
theorem toEquivalence.inv.app (h : PointwiseEquivalence η) (a : B) :
    h.toEquivalence.inv.app a = h.invApp a := sorry

/-- The forward unit cell of the assembled equivalence is the supplied pointwise unit cell. -/
@[simp]
theorem toEquivalence.unit.hom.app (h : PointwiseEquivalence η) (a : B) :
    h.toEquivalence.unit.hom.as.app a = (h.unit a).hom := sorry

/-- The inverse unit cell of the assembled equivalence is the inverse supplied pointwise unit
cell. -/
@[simp]
theorem toEquivalence.unit.inv.app (h : PointwiseEquivalence η) (a : B) :
    h.toEquivalence.unit.inv.as.app a = (h.unit a).inv := sorry

/-- The forward counit cell of the assembled equivalence is the supplied pointwise counit
cell. -/
@[simp]
theorem toEquivalence.counit.hom.app (h : PointwiseEquivalence η) (a : B) :
    h.toEquivalence.counit.hom.as.app a = (h.counit a).hom := sorry

/-- The inverse counit cell of the assembled equivalence is the inverse supplied pointwise
counit cell. -/
@[simp]
theorem toEquivalence.counit.inv.app (h : PointwiseEquivalence η) (a : B) :
    h.toEquivalence.counit.inv.as.app a = (h.counit a).inv := sorry

/-- Evaluating the assembled functor-bicategory equivalence recovers the supplied pointwise
equivalence. -/
@[simp]
theorem toEquivalence.app (h : PointwiseEquivalence η) (a : B) :
    h.toEquivalence.app a = h.app a := sorry

/-- Extracting pointwise equivalence data from the equivalence assembled from it recovers
the original data. -/
@[simp]
theorem toEquivalence.ofEquivalence (h : PointwiseEquivalence η) :
    ofEquivalence h.toEquivalence = h := sorry

/-- Assembling the pointwise data extracted from a functor-bicategory equivalence recovers
the original equivalence. -/
@[simp]
theorem ofEquivalence.toEquivalence (e : F ≌ G) :
    (ofEquivalence e).toEquivalence = e := sorry

/- Data audit (mathlib 4.32): `unitIso` and `counitIso` retain the supplied
pointwise isomorphisms componentwise; `toEquivalence` retains `η` literally as
its forward transformation. Any `sorryAx` is confined to mate compatibility,
coherence, and round-trip equality fields. -/

end PointwiseEquivalence

end Pseudofunctor.StrongTrans

end CategoryTheory
