/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelativeGroupLawGrpObj.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.

Selective ReasLib adaptation from NYLL commit
8c1b16d10afaca09e0dc72753c6575e230d31a55.
The canonical group data are now Mathlib GrpObj over an arbitrary base scheme.
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.Algebra.Group.TransferInstance

/-!
# Actual relative points of a group scheme

The canonical data owner is Mathlib's `GrpObj G`, with `G : Over S`.
The group on `T ⟶ G` and its restriction maps are Mathlib's `yonedaGrpObj`.
The subtype presentation used by relative group laws is a view of these same
points; it stores no second group law. No geometric hypotheses are required.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.GroupObject

variable {S : Scheme.{u}} (G : Over S)

/-- Morphisms over `S`, displayed as scheme morphisms satisfying their base equation. -/
abbrev RelativePoints (T : Over S) :=
  {x : T.left ⟶ G.left // x ≫ G.hom = T.hom}

/-- The canonical comparison with the subtype of relative scheme morphisms. -/
def relativePointsEquiv (T : Over S) : (T ⟶ G) ≃ RelativePoints G T where
  toFun x := ⟨x.left, Over.w x⟩
  invFun x := Over.homMk x.1 x.2
  left_inv x := Over.homMk_eta x _
  right_inv _ := Subtype.ext rfl

@[simp]
theorem relativePointsEquiv_apply_val (T : Over S) (x : T ⟶ G) :
    (relativePointsEquiv G T x).1 = x.left := rfl

@[simp]
theorem relativePointsEquiv_symm_left (T : Over S) (x : RelativePoints G T) :
    ((relativePointsEquiv G T).symm x).left = x.1 := rfl

/-- Restriction in the subtype presentation is actual precomposition of schemes. -/
def restrictRelativePoints {T T' : Over S} (a : T' ⟶ T)
    (x : RelativePoints G T) : RelativePoints G T' :=
  ⟨a.left ≫ x.1, by rw [Category.assoc, x.2]; exact Over.w a⟩

@[simp]
theorem relativePointsEquiv_natural {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G) :
    relativePointsEquiv G T' (a ≫ x) =
      restrictRelativePoints G a (relativePointsEquiv G T x) := rfl

variable [GrpObj G]

/-- The subtype point group is transported from the canonical Mathlib point group. -/
@[instance_reducible]
def relativePointGroup (T : Over S) : Group (RelativePoints G T) :=
  (relativePointsEquiv G T).symm.group

/-- The relative-point view preserves the actual group law. -/
def relativePointsMulEquiv (T : Over S) :
    letI := relativePointGroup G T
    (T ⟶ G) ≃* RelativePoints G T :=
  letI := relativePointGroup G T
  (relativePointsEquiv G T).symm.mulEquiv.symm

@[simp]
theorem relativePointsMulEquiv_apply (T : Over S) (x : T ⟶ G) :
    letI := relativePointGroup G T
    relativePointsMulEquiv G T x = relativePointsEquiv G T x := rfl

/-- The group-valued functor of points; all operations are owned by Mathlib. -/
abbrev pointsFunctor : (Over S)ᵒᵖ ⥤ GrpCat.{u} := yonedaGrpObj G

@[simp]
theorem pointsFunctor_map {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G) :
    (pointsFunctor G).map a.op x = a ≫ x := rfl

/-- The additive notation for the same actual point group, for arithmetic consumers. -/
abbrev AdditivePoints (T : Over S) := Additive (T ⟶ G)

end AlgebraicGeometry.Scheme.GroupObject
