/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
public import ReasLib.RingTheory.Normal.GeometricallyNormal

/-!
# Geometrically normal schemes over a field

This leaf owns pointwise and global geometric normality for schemes over a
field, together with equivalent stalk-algebra criteria.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : Over (Spec (CommRingCat.of k)))

/-- A scheme over a field is geometrically normal at a point when every local
ring above that point after every field extension is normal. -/
@[stacks 038M]
abbrev geometricallyNormalAt (x : X.left) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
    ∀ x' : FieldExtension.baseChange k K X.hom,
      FieldExtension.toSource k K X.hom x' = x →
        IsNormalRing ((FieldExtension.baseChange k K X.hom).presheaf.stalk x')

/-- Unfold geometric normality at a point into normality of the local rings at
all field-extension points lying above it. -/
@[stacks 038M, simp]
theorem geometricallyNormalAt_iff (x : X.left) :
    geometricallyNormalAt X x ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ∀ x' : FieldExtension.baseChange k K X.hom,
          FieldExtension.toSource k K X.hom x' = x →
            IsNormalRing ((FieldExtension.baseChange k K X.hom).presheaf.stalk x') := sorry

/-- A scheme geometrically normal at a point has normal local rings at all
field-extension points lying above it. -/
@[stacks 038M]
theorem geometricallyNormalAt.isNormalRing_stalk {x : X.left}
    (hx : geometricallyNormalAt X x) :
    ∀ (K : Type u) [Field K] [Algebra k K],
      ∀ x' : FieldExtension.baseChange k K X.hom,
        FieldExtension.toSource k K X.hom x' = x →
          IsNormalRing ((FieldExtension.baseChange k K X.hom).presheaf.stalk x') := sorry

/-- A scheme over a field is geometrically normal when it is geometrically normal at every point. -/
@[stacks 038M]
abbrev geometricallyNormal : Prop :=
  ∀ x : X.left, geometricallyNormalAt X x

/-- Unfold geometric normality over the base field into pointwise geometric
normality. -/
@[stacks 038M, simp]
theorem geometricallyNormal_iff :
    geometricallyNormal X ↔ ∀ x : X.left, geometricallyNormalAt X x := sorry

/-- A geometrically normal scheme is geometrically normal at each of its points. -/
@[stacks 038M]
theorem geometricallyNormal.geometricallyNormalAt
    (hX : geometricallyNormal X) (x : X.left) :
    geometricallyNormalAt X x := sorry

/-- Geometric normality at a point is equivalent to geometric normality of its
local ring as an algebra over the base field. -/
@[stacks 038M]
theorem geometricallyNormalAt_iff_isGeometricallyNormal (x : X.left) :
    geometricallyNormalAt X x ↔
      Algebra.IsGeometricallyNormal k (X.left.presheaf.stalk x) := sorry

/-- A scheme over a field is geometrically normal exactly when every local
ring is geometrically normal as an algebra over the base field. -/
@[stacks 038M]
theorem geometricallyNormal_iff_forall_isGeometricallyNormal :
    geometricallyNormal X ↔
      ∀ x : X.left, Algebra.IsGeometricallyNormal k (X.left.presheaf.stalk x) := sorry

/-- The affine-open section rings of a scheme over a field are geometrically normal when each is
geometrically normal over the base field through its canonical section-ring algebra. -/
@[stacks 038O]
def affineOpenSectionsGeometricallyNormal : Prop :=
  ∀ U : X.left.affineOpens,
    Algebra.IsGeometricallyNormal k (sectionsAlg X (U : X.left.Opens))

/-- Unfold the affine-open section-ring formulation of geometric normality over the base field. -/
@[stacks 038O]
theorem affineOpenSectionsGeometricallyNormal_iff :
    affineOpenSectionsGeometricallyNormal X ↔
      ∀ U : X.left.affineOpens,
        Algebra.IsGeometricallyNormal k (sectionsAlg X (U : X.left.Opens)) := sorry

end AlgebraicGeometry.SchemeOverField
