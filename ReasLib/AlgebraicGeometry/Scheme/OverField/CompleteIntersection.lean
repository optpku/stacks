/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.RingTheory.CompleteIntersection.Basic
public import ReasLib.RingTheory.CompleteIntersection.OverField

/-!
# Complete-intersection schemes over a field

This module relates complete-intersection conditions on a scheme over a field to
conditions on affine coordinate algebras and local rings.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

namespace AffineOpen

/-- An affine open of a scheme over `k` is a local complete intersection when its
canonical section algebra over `k` is a local complete intersection. -/
def IsLocalCompleteIntersection
    (X : SchemeOverField k) (U : X.left.affineOpens) : Prop :=
  _root_.IsLocalCompleteIntersection k (Scheme.Hom.sectionsAlgOverSpec X.hom U)

/-- An affine open of a scheme over `k` is a global complete intersection when its
canonical section algebra over `k` is a global complete intersection. -/
def IsGlobalCompleteIntersection
    (X : SchemeOverField k) (U : X.left.affineOpens) : Prop :=
  _root_.IsGlobalCompleteIntersection k (Scheme.Hom.sectionsAlgOverSpec X.hom U)

/-- Every affine open that is a global complete intersection over a field is a local complete
intersection over that field. -/
theorem IsGlobalCompleteIntersection.isLocal
    {X : SchemeOverField k} {U : X.left.affineOpens}
    (hU : IsGlobalCompleteIntersection X U) :
    IsLocalCompleteIntersection X U := sorry

end AffineOpen

/-- A point has an affine local-complete-intersection neighborhood if it lies in an affine open
whose canonical coordinate algebra is a local complete intersection over the base field. -/
def HasAffineLocalCompleteIntersectionNeighborhood
    (X : SchemeOverField k) (x : X.left) : Prop :=
  ∃ U : X.left.affineOpens, x ∈ (U : X.left.Opens) ∧
    AffineOpen.IsLocalCompleteIntersection X U

/-- A scheme over a field has affine local-complete-intersection neighborhoods when every point
has such a neighborhood. -/
def HasAffineLocalCompleteIntersectionNeighborhoods
    (X : SchemeOverField k) : Prop :=
  ∀ x : X.left, HasAffineLocalCompleteIntersectionNeighborhood X x

/-- A scheme over a field is a local complete intersection exactly when every point has an
affine local-complete-intersection neighborhood. -/
theorem localCompleteIntersection_iff_affineLocally
    (X : SchemeOverField k) :
    IsLocalCompleteIntersectionOver k X.hom ↔
      HasAffineLocalCompleteIntersectionNeighborhoods X := sorry

/-- A point has an affine global-complete-intersection neighborhood if it lies in an affine open
whose canonical coordinate algebra is a global complete intersection over the base field. -/
def HasAffineGlobalCompleteIntersectionNeighborhood
    (X : SchemeOverField k) (x : X.left) : Prop :=
  ∃ U : X.left.affineOpens, x ∈ (U : X.left.Opens) ∧
    AffineOpen.IsGlobalCompleteIntersection X U

/-- A point with an affine global-complete-intersection neighborhood also has an affine
local-complete-intersection neighborhood. -/
theorem HasAffineGlobalCompleteIntersectionNeighborhood.hasLocal
    {X : SchemeOverField k} {x : X.left}
    (hx : HasAffineGlobalCompleteIntersectionNeighborhood X x) :
    HasAffineLocalCompleteIntersectionNeighborhood X x := sorry

/-- A scheme over a field has affine global-complete-intersection neighborhoods when every point
has such a neighborhood. -/
def HasAffineGlobalCompleteIntersectionNeighborhoods
    (X : SchemeOverField k) : Prop :=
  ∀ x : X.left, HasAffineGlobalCompleteIntersectionNeighborhood X x

/-- Affine global-complete-intersection neighborhoods yield affine
local-complete-intersection neighborhoods at every point. -/
theorem HasAffineGlobalCompleteIntersectionNeighborhoods.hasLocal
    {X : SchemeOverField k}
    (hX : HasAffineGlobalCompleteIntersectionNeighborhoods X) :
    HasAffineLocalCompleteIntersectionNeighborhoods X := sorry

/-- A scheme over a field has complete-intersection stalks when each canonical stalk algebra is
a complete intersection over the base field. -/
def HasCompleteIntersectionStalks (X : SchemeOverField k) : Prop :=
  ∀ x : X.left, Algebra.IsCompleteIntersectionOver k (stalkRing X x)

/-- For a scheme locally of finite type over a field, being a local complete intersection,
having affine global-complete-intersection neighborhoods, and having complete-intersection
stalks over the field are equivalent. -/
theorem localCompleteIntersection_tfae
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    List.TFAE
      [ IsLocalCompleteIntersectionOver k X.hom
      , HasAffineGlobalCompleteIntersectionNeighborhoods X
      , HasCompleteIntersectionStalks X
      ] := sorry

end AlgebraicGeometry.SchemeOverField
