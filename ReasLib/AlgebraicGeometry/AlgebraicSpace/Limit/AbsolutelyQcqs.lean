module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Directed absolutely quasi-separated affine-transition limits

A specified limit cone for a directed inverse system of quasi-compact,
absolutely quasi-separated algebraic spaces with affine transition morphisms,
together with a distinguished index.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- A specified limit cone for a directed inverse system of quasi-compact,
absolutely quasi-separated algebraic spaces with affine transition morphisms,
together with a distinguished index. -/
structure AbsolutelyQcqsAffineLimit {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))] where
  /-- The specified limiting cone. -/
  limitCone : LimitCone D
  /-- The distinguished index of the inverse system. -/
  base : I

namespace AbsolutelyQcqsAffineLimit

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- Construct an absolutely quasi-separated affine-transition limit from a specified limiting cone
and distinguished index. -/
def ofCone (c : Cone D) (hc : IsLimit c) (i0 : I) : AbsolutelyQcqsAffineLimit D where
  limitCone := ⟨c, hc⟩
  base := i0

/-- The cone, limiting proof, and distinguished index of `ofCone` are the specified inputs. -/
theorem ofCone_spec (c : Cone D) (hc : IsLimit c) (i0 : I) :
    (ofCone D c hc i0).limitCone.cone = c ∧
      (ofCone D c hc i0).limitCone.isLimit = hc ∧
      (ofCone D c hc i0).base = i0 := sorry

end AbsolutelyQcqsAffineLimit

end AlgebraicGeometry.AlgebraicSpace.Limit
