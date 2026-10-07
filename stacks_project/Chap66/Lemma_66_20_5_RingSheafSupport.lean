module

public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Remark_66_19_11_StalkFunctor

/-!
# Support of a sheaf of rings on the small étale site

The geometric stalk of a ring sheaf at a geometric point of an algebraic space is
inverse image along the point morphism, followed by sections over the source spectrum.
The support is the locus in `|X|` where this stalk is a nonzero ring, equivalently
where the unit is nonzero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The opposite of étale base change admits left Kan extensions of ring-valued
presheaves. -/
instance etaleBaseChange_op_hasLeftKanExtension_ringCat {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : (smallEtaleSite Y)ᵒᵖ ⥤ RingCat.{u}) :
    (etaleBaseChange f).op.HasLeftKanExtension F :=
  sorry

/-- Ring-valued weak sheafification exists on the étale site of algebraic spaces. -/
instance spacesEtaleTopology_hasWeakSheafify_ringCat (X : AlgebraicSpace S) :
    HasWeakSheafify (spacesEtaleTopology X) RingCat.{u} :=
  sorry

variable {X : AlgebraicSpace S}

/-- Sections over `Spec(p.K)`, sending a sheaf of rings on the small étale site of the source
to its value on the identity object. -/
def ringSectionsFunctor (p : FieldValuedPoint X) :
    Sheaf (smallEtaleTopology (ofOver p.overObj)) RingCat.{u} ⥤ RingCat.{u} :=
  sheafToPresheaf (smallEtaleTopology (ofOver p.overObj)) RingCat.{u} ⋙
    (evaluation (smallEtaleSite (ofOver p.overObj))ᵒᵖ RingCat.{u}).obj (op p.sourceObj)

/-- Sections of a sheaf of rings over the identity object of `Spec(p.K)`. -/
theorem ringSectionsFunctor_obj (p : FieldValuedPoint X)
    (G : Sheaf (smallEtaleTopology (ofOver p.overObj)) RingCat.{u}) :
    (ringSectionsFunctor p).obj G = G.obj.obj (op p.sourceObj) :=
  sorry

/-- The geometric stalk of a sheaf of rings at a geometric point, as inverse image along the
point morphism followed by sections over `Spec(k)`. -/
def ringGeometricStalk (F : Sheaf (smallEtaleTopology X) RingCat.{u})
    (xbar : GeometricPoint X) : RingCat.{u} :=
  (ringSectionsFunctor xbar.toFieldValuedPoint).obj
    ((sheafInverseImage RingCat.{u} xbar.hom).obj F)

/-- The geometric stalk of a sheaf of rings is inverse image along `xbar.hom`, then sections
over `Spec(k)`. -/
theorem ringGeometricStalk_eq (F : Sheaf (smallEtaleTopology X) RingCat.{u})
    (xbar : GeometricPoint X) :
    ringGeometricStalk F xbar =
      (ringSectionsFunctor xbar.toFieldValuedPoint).obj
        ((sheafInverseImage RingCat.{u} xbar.hom).obj F) :=
  sorry

/-- The support of a sheaf of rings on the small étale site, as the points of `|X|` admitting a
geometric point whose geometric stalk is a nonzero ring. -/
def ringSheafSupport (F : Sheaf (smallEtaleTopology X) RingCat.{u}) : Set (Points X) :=
  {x | ∃ xbar : GeometricPoint X, xbar.image = x ∧ (1 : ringGeometricStalk F xbar) ≠ 0}

/-- Membership in the support of a sheaf of rings is existence of a geometric point over the
point at which the unit of the geometric stalk is nonzero. -/
theorem mem_ringSheafSupport_iff (F : Sheaf (smallEtaleTopology X) RingCat.{u}) (x : Points X) :
    x ∈ ringSheafSupport F ↔
      ∃ xbar : GeometricPoint X, xbar.image = x ∧ (1 : ringGeometricStalk F xbar) ≠ 0 :=
  sorry

/-- Whether the unit vanishes in the geometric stalk of a sheaf of rings depends only on the
image point in `|X|`. -/
theorem ringGeometricStalk_one_eq_zero_iff_of_image_eq
    (F : Sheaf (smallEtaleTopology X) RingCat.{u}) (xbar tbar : GeometricPoint X)
    (himage : xbar.image = tbar.image) :
    (1 : ringGeometricStalk F xbar) = 0 ↔ (1 : ringGeometricStalk F tbar) = 0 :=
  sorry

/-- For any geometric point, support membership of its image is equivalent to nonvanishing of
the unit in its geometric stalk. -/
theorem mem_ringSheafSupport_iff_one_ne_zero
    (F : Sheaf (smallEtaleTopology X) RingCat.{u}) (xbar : GeometricPoint X) :
    xbar.image ∈ ringSheafSupport F ↔ (1 : ringGeometricStalk F xbar) ≠ 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
