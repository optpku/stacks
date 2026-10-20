/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The size of a scheme is the supremum of the countable cardinal, the cardinality
of its affine opens, and the cardinalities of their section rings. -/
noncomputable def size (X : Scheme.{u}) : Cardinal.{u} :=
  ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(Γ(X, U))

/-- The countable cardinal is bounded by the size of any scheme. -/
lemma aleph0_le_size (X : Scheme.{u}) : ℵ₀ ≤ X.size := sorry

/-- The cardinality of the affine opens of a scheme is bounded by its size. -/
lemma cardinalMk_affineOpens_le_size (X : Scheme.{u}) : #X.affineOpens ≤ X.size := sorry

/-- The cardinality of the section ring over any affine open is bounded by the
size of the scheme. -/
lemma cardinalMk_sections_le_size (X : Scheme.{u}) (U : X.affineOpens) :
    #(Γ(X, U)) ≤ X.size := sorry

/-- The size of an affine scheme is the supremum of the cardinality of its global
section ring and the countable cardinal. -/
theorem size_of_isAffine (S : Scheme.{u}) [IsAffine S] :
    S.size = #(Γ(S, ⊤)) ⊔ ℵ₀ := sorry

/-- The size of the spectrum of a commutative ring is the supremum of the
cardinality of the ring and the countable cardinal. -/
theorem size_Spec (R : CommRingCat.{u}) : (Spec R).size = #R ⊔ ℵ₀ := sorry

/-- The size of a scheme is bounded by the maximum of the countable cardinal,
the cardinality of an open cover's index type, and the supremum of the sizes of
the covering open subschemes. -/
theorem size_le_isOpenCover {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) :
    X.size ≤ max ℵ₀ (max (#ι) (⨆ i, (U i).toScheme.size)) := sorry

/-- The size of a scheme is bounded by the maximum of the index cardinal of a
nonempty-indexed open cover and the supremum of the sizes of the covering schemes. -/
theorem size_le_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) (hI : Nonempty 𝒰.I₀) :
    X.size ≤ max (#𝒰.I₀) (⨆ i, (𝒰.X i).size) := sorry

/-- A locally finite-type morphism with quasi-compact source bounds the size of
the source scheme by the size of the target scheme. -/
theorem size_le_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [CompactSpace X] :
    X.size ≤ S.size := sorry

/-- The size of the fibre product of two morphisms of schemes is bounded by
the maximum of the sizes of their source schemes. -/
theorem size_pullback_le {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    (pullback f g).size ≤ max X.size Y.size := sorry

/-- The size of a scheme presenting a fibre product is bounded by the maximum
of the sizes of the two schemes over the base. -/
theorem size_le_of_isPullback {X Y S P : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {fst : P ⟶ X} {snd : P ⟶ Y} (h : IsPullback fst snd f g) :
    P.size ≤ max X.size Y.size := sorry

/-- The size of a scheme is the maximum of the countable cardinal, the cardinality
of its affine opens, and the supremum of their section-ring cardinalities. -/
theorem size_eq (X : Scheme.{u}) :
    size X = max (max ℵ₀ (#X.affineOpens)) (⨆ U : X.affineOpens, #(Γ(X, U))) := by
  rfl

/-- Isomorphic schemes have the same size. -/
theorem size_eq_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) : size X = size Y := sorry

/-- The object property of schemes of size at most `κ`. -/
def sizeLE (κ : Cardinal.{u}) : ObjectProperty Scheme.{u} :=
  fun X ↦ X.size ≤ κ

/-- Membership in `sizeLE κ` is the inequality `size X ≤ κ`. -/
theorem sizeLE_iff (κ : Cardinal.{u}) (X : Scheme.{u}) :
    sizeLE κ X ↔ X.size ≤ κ := by
  rfl

namespace sizeLE

/-- The property of having size at most `κ` is invariant under isomorphism of schemes. -/
instance instIsClosedUnderIsomorphisms (κ : Cardinal.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (sizeLE κ) := sorry

/-- Schemes of size at most `κ` form an essentially small object property in universe `u`. -/
instance essentiallySmall (κ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u} (sizeLE κ) := sorry

end sizeLE

/-- For every cardinal `κ`, a small family of schemes represents every scheme of size
at most `κ` up to isomorphism. -/
theorem exists_small_of_size_le (κ : Cardinal.{u}) :
    ∃ (A : Type u) (X : A → Scheme.{u}),
      ∀ S : Scheme.{u}, S.size ≤ κ → ∃ a, Nonempty (X a ≅ S) := sorry

end AlgebraicGeometry.Scheme
