/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Reduced
public import ReasLib.FieldTheory.PurelyInseparable.PerfectClosure
public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.PurelyInseparable
public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.TensorProduct

/-!
# Criteria for geometrically reduced schemes over a field

This leaf gives field-extension and affine-open criteria for geometric reducedness of a scheme
over a field of positive characteristic.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry PerfectClosure

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- For a scheme over a field of positive characteristic, geometric reducedness is equivalent to
reducedness after every field extension, after every finite purely inseparable field extension,
after base change to the first Frobenius-root extension, the perfect closure, or an algebraic
closure, and to geometric reducedness of every affine-open section algebra. -/
@[stacks 035X]
theorem geometricallyReduced_tfae
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (X : Over (Spec (CommRingCat.of k))) :
    List.TFAE [
      geometricallyReduced X,
      ∀ (k' : Type u) [Field k'] [Algebra k k'],
        IsReduced (FieldExtension.baseChange k k' X.hom),
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsReduced (FieldExtension.baseChange k k' X.hom),
      IsReduced
        (FieldExtension.baseChange k (IntermediateField.onePthRootExtension k p) X.hom),
      IsReduced (FieldExtension.baseChange k (kᵖᵉʳᶠ) X.hom),
      IsReduced (FieldExtension.baseChange k (AlgebraicClosure k) X.hom),
      ∀ U : X.left.affineOpens,
        Algebra.IsGeometricallyReduced k
          (SchemeOverField.sectionsAlg X (U : X.left.Opens))
    ] := sorry

/-- A scheme over a field of prime characteristic is geometrically reduced if and only if its
relative Frobenius target is reduced. -/
@[stacks 0CCE]
theorem geometricallyReduced_iff_isReduced_relativeFrobeniusTarget
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (X : Over (Spec (CommRingCat.of k))) :
    geometricallyReduced X ↔
      IsReduced (Scheme.Hom.relativeFrobeniusTarget (p := p) X.hom) := sorry

end AlgebraicGeometry.SchemeOverField
