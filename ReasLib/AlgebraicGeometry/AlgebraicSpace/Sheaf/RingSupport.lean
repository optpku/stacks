/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.ConcreteHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Constructible

/-!
# Support of ring sheaves on algebraic spaces

The support is the locus of nonzero geometric stalks. Geometric stalks are formed by
ring inverse image along the geometric point, followed by sections over its source spectrum.
The support is closed in the canonical topology on algebraic-space points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Sections over `Spec(p.K)` evaluate a ring sheaf at the identity object of the source's
small étale site. -/
def ringSectionsFunctor (p : FieldValuedPoint X) :
    Sheaf (smallEtaleTopology (ofOver p.overObj)) RingCat.{u} ⥤ RingCat.{u} :=
  sheafToPresheaf (smallEtaleTopology (ofOver p.overObj)) RingCat.{u} ⋙
    (evaluation (smallEtaleSite (ofOver p.overObj))ᵒᵖ RingCat.{u}).obj (op p.sourceObj)

/-- Sections of a ring sheaf over the source spectrum are its value at the identity object. -/
theorem ringSectionsFunctor_obj (p : FieldValuedPoint X)
    (G : Sheaf (smallEtaleTopology (ofOver p.overObj)) RingCat.{u}) :
    (ringSectionsFunctor p).obj G = G.obj.obj (op p.sourceObj) :=
  rfl

/-- The geometric stalk of a ring sheaf is its ring inverse image along the geometric point,
evaluated over the source spectrum. -/
def ringGeometricStalk (F : Sheaf (smallEtaleTopology X) RingCat.{u})
    (xbar : GeometricPoint X) : RingCat.{u} :=
  (ringSectionsFunctor xbar.toFieldValuedPoint).obj
    (((EtaleRingedTopos.topos xbar.hom).ringInverseImage).obj F)

/-- A geometric stalk is obtained by ring inverse image and source-spectrum sections. -/
theorem ringGeometricStalk_eq (F : Sheaf (smallEtaleTopology X) RingCat.{u})
    (xbar : GeometricPoint X) :
    ringGeometricStalk F xbar =
      (ringSectionsFunctor xbar.toFieldValuedPoint).obj
        (((EtaleRingedTopos.topos xbar.hom).ringInverseImage).obj F) :=
  rfl

/-- The support of a ring sheaf is the set of points admitting a geometric point with
nonzero unit in its geometric stalk. -/
def ringSheafSupport (F : Sheaf (smallEtaleTopology X) RingCat.{u}) : Set (Points X) :=
  {x | ∃ xbar : GeometricPoint X, xbar.image = x ∧ (1 : ringGeometricStalk F xbar) ≠ 0}

/-- Support membership means that some geometric point above the point has nonzero unit
in its geometric stalk. -/
theorem mem_ringSheafSupport_iff (F : Sheaf (smallEtaleTopology X) RingCat.{u}) (x : Points X) :
    x ∈ ringSheafSupport F ↔
      ∃ xbar : GeometricPoint X, xbar.image = x ∧ (1 : ringGeometricStalk F xbar) ≠ 0 :=
  by rfl

/-- Whether the unit vanishes in a geometric stalk depends only on the image point. -/
theorem ringGeometricStalk_one_eq_zero_iff_of_image_eq
    (F : Sheaf (smallEtaleTopology X) RingCat.{u}) (xbar tbar : GeometricPoint X)
    (himage : xbar.image = tbar.image) :
    (1 : ringGeometricStalk F xbar) = 0 ↔ (1 : ringGeometricStalk F tbar) = 0 :=
  sorry

/-- The image of any geometric point belongs to the support exactly when the unit in its
geometric stalk is nonzero. -/
theorem mem_ringSheafSupport_iff_one_ne_zero
    (F : Sheaf (smallEtaleTopology X) RingCat.{u}) (xbar : GeometricPoint X) :
    xbar.image ∈ ringSheafSupport F ↔ (1 : ringGeometricStalk F xbar) ≠ 0 :=
  sorry

/-- Inverse images of ring-sheaf support along representable étale morphisms from schemes
are closed. -/
theorem isClosed_schemePreimage_ringSheafSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) RingCat.{u}) {U : Over S} (f : ofOver U ⟶ X)
    (hf : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f) :
    IsClosed (schemePreimage f (ringSheafSupport F)) :=
  sorry

/-- The support of a ring sheaf on the small étale site of an algebraic space is closed
in the canonical topology on its points. -/
theorem isClosed_ringSheafSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) RingCat.{u}) :
    IsClosed (ringSheafSupport F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
