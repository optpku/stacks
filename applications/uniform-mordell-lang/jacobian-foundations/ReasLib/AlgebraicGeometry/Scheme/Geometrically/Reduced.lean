module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.Perfect

/-!
# Geometrically reduced schemes over a field

This leaf records the pointwise field-extension formulation of geometric
reducedness and bridges it to mathlib's morphism-level owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

noncomputable section

variable {k : Type u} [Field k]

/-- For an affine scheme over a field, morphism-level geometric reducedness agrees
with geometric reducedness of its coordinate ring over the field. -/
@[stacks 030S]
theorem geometricallyReduced_spec_iff_isGeometricallyReduced
    {S : Type u} [CommRing S] [Algebra k S] :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k S))) ↔
      Algebra.IsGeometricallyReduced k S := sorry

variable (X : Over (Spec (CommRingCat.of k)))

/-- A scheme `X` over `k` is geometrically reduced at `x` when the local ring at
every point above `x` after every field-extension base change is reduced. -/
@[stacks 035V]
abbrev geometricallyReducedAt (x : X.left) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
      ∀ x' : FieldExtension.baseChange k K X.hom,
      FieldExtension.toSource k K X.hom x' = x →
        _root_.IsReduced ((FieldExtension.baseChange k K X.hom).presheaf.stalk x')

/-- Unfold geometric reducedness at `x` into the reduced-stalk condition on all
field-extension base changes above `x`. -/
@[stacks 035V, simp]
theorem geometricallyReducedAt_iff (x : X.left) :
    geometricallyReducedAt X x ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ∀ x' : FieldExtension.baseChange k K X.hom,
          FieldExtension.toSource k K X.hom x' = x →
            _root_.IsReduced ((FieldExtension.baseChange k K X.hom).presheaf.stalk x') := sorry

/-- A scheme geometrically reduced at `x` has reduced local rings at every
field-extension point above `x`. -/
@[stacks 035V]
theorem geometricallyReducedAt.isReduced_stalk {x : X.left}
    (hx : geometricallyReducedAt X x) :
    ∀ (K : Type u) [Field K] [Algebra k K],
      ∀ x' : FieldExtension.baseChange k K X.hom,
        FieldExtension.toSource k K X.hom x' = x →
          _root_.IsReduced ((FieldExtension.baseChange k K X.hom).presheaf.stalk x') := sorry

/-- A scheme over `k` is geometrically reduced when it is geometrically reduced
at every point. -/
@[stacks 035V]
abbrev geometricallyReduced : Prop :=
  ∀ x : X.left, geometricallyReducedAt X x

/-- Unfold geometric reducedness over `k` into pointwise geometric reducedness. -/
@[stacks 035V, simp]
theorem geometricallyReduced_iff :
    geometricallyReduced X ↔ ∀ x : X.left, geometricallyReducedAt X x := sorry

/-- A geometrically reduced scheme is geometrically reduced at each of its points. -/
@[stacks 035V]
theorem geometricallyReduced.geometricallyReducedAt
    (hX : geometricallyReduced X) (x : X.left) :
    geometricallyReducedAt X x := sorry

/-- The pointwise field-extension formulation of geometric reducedness agrees with
mathlib's morphism-level predicate `GeometricallyReduced X.hom`. -/
@[stacks 035V]
theorem geometricallyReduced_iff_morphismGeometricallyReduced :
    geometricallyReduced X ↔ GeometricallyReduced X.hom := sorry

/-- Geometric reducedness over `k` can equivalently be checked by reducedness of
every field-extension base change. -/
@[stacks 035V]
theorem geometricallyReduced_iff_forall_isReduced_fieldExtensionBaseChange :
    geometricallyReduced X ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IsReduced (FieldExtension.baseChange k K X.hom) := sorry

/-- Geometric reducedness at `x` agrees with geometric reducedness of the local
ring `𝒪_{X,x}` over the base field. -/
@[stacks 035W]
theorem geometricallyReducedAt_iff_isGeometricallyReduced
    (x : X.left) :
    geometricallyReducedAt X x ↔
      Algebra.IsGeometricallyReduced k (X.left.presheaf.stalk x) := sorry

variable [PerfectField k]

/-- Over a perfect field, a reduced local ring gives geometric reducedness at the
corresponding point. -/
@[stacks 020I]
theorem geometricallyReducedAt_of_isReduced_stalk_of_perfectField
    (x : X.left) [_root_.IsReduced (X.left.presheaf.stalk x)] :
    geometricallyReducedAt X x := sorry

/-- Over a perfect field, a reduced scheme is geometrically reduced over the base
field. -/
@[stacks 020I]
theorem geometricallyReduced_of_isReduced_of_perfectField
    (X : Over (Spec (CommRingCat.of k))) [IsReduced X.left] :
    geometricallyReduced X := sorry

end

end AlgebraicGeometry.SchemeOverField
