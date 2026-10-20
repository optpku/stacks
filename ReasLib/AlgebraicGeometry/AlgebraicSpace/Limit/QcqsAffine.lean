/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Directed qcqs affine-transition limits of algebraic spaces

A specified limit cone for a directed inverse system of quasi-compact,
quasi-separated algebraic spaces with affine transition morphisms, together
with a distinguished index.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- A specified limit cone for a directed inverse system of quasi-compact,
quasi-separated algebraic spaces with affine transition morphisms, together
with a distinguished index. -/
structure QcqsAffineLimit {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))] where
  /-- The specified limiting cone. -/
  limitCone : LimitCone D
  /-- The distinguished index of the inverse system. -/
  base : I

namespace QcqsAffineLimit

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- Construct a qcqs affine-transition limit from a specified limiting cone and index. -/
def ofCone (c : Cone D) (hc : IsLimit c) (i0 : I) : QcqsAffineLimit D where
  limitCone := ⟨c, hc⟩
  base := i0

/-- The cone and distinguished index of `ofCone` are the specified ones, and its cone is limiting. -/
theorem ofCone_spec (c : Cone D) (hc : IsLimit c) (i0 : I) :
    (ofCone D c hc i0).limitCone.cone = c ∧
      (ofCone D c hc i0).limitCone.isLimit = hc ∧
      (ofCone D c hc i0).base = i0 := ⟨rfl, rfl, rfl⟩

section

variable {D' : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ i, IsQuasiCompact (D'.obj i)] [∀ i, IsQuasiSeparated (D'.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D'.map (homOfLE h))]

/-- Replace the distinguished base stage of a specified qcqs affine limit. -/
def withBase (s : QcqsAffineLimit D') (i : I) : QcqsAffineLimit D' where
  limitCone := s.limitCone
  base := i

/-- Replacing the base stage preserves the specified limiting cone. -/
theorem withBase_limitCone (s : QcqsAffineLimit D') (i : I) :
    (withBase s i).limitCone = s.limitCone := rfl

/-- Replacing the base stage records the requested new base. -/
theorem withBase_base (s : QcqsAffineLimit D') (i : I) :
    (withBase s i).base = i := rfl

end

end QcqsAffineLimit

end AlgebraicGeometry.AlgebraicSpace.Limit
