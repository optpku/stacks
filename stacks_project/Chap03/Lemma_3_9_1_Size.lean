/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap03.Lemma_3_9_4_Size
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Unfolding of `size`. -/
theorem size_eq (X : Scheme.{u}) :
    size X = max (max ℵ₀ (#X.affineOpens)) (⨆ U : X.affineOpens, #(Γ(X, U))) := sorry

/-- The size of a scheme is at least the cardinality of its set of affine opens. -/
theorem mk_affineOpens_le_size (X : Scheme.{u}) : #X.affineOpens ≤ size X := sorry

/-- The size of a scheme is at least the cardinality of the section ring of any affine open. -/
theorem mk_sections_le_size (X : Scheme.{u}) (U : X.affineOpens) :
    #(Γ(X, U)) ≤ size X := sorry

/-- Isomorphic schemes have the same size. -/
theorem size_eq_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) : size X = size Y := sorry

/-- The object property of schemes of size at most `κ`. -/
def sizeLE (κ : Cardinal.{u}) : ObjectProperty Scheme.{u} :=
  fun X ↦ X.size ≤ κ

/-- Membership in `sizeLE κ` is the inequality `size X ≤ κ`. -/
theorem sizeLE_iff (κ : Cardinal.{u}) (X : Scheme.{u}) :
    sizeLE κ X ↔ X.size ≤ κ := sorry

namespace sizeLE

/-- The property of having size at most `κ` is invariant under isomorphism of schemes. -/
instance instIsClosedUnderIsomorphisms (κ : Cardinal.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (sizeLE κ) := sorry

/-- Schemes of size at most `κ` form an essentially small object property in universe `u`. -/
instance essentiallySmall (κ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u} (sizeLE κ) := sorry

end sizeLE

end AlgebraicGeometry.Scheme
