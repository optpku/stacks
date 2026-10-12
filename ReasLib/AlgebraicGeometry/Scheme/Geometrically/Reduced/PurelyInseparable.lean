/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.PurelyInseparable

/-!
# Pointwise purely inseparable tests for geometric reducedness

This module records field-extension criteria for geometric reducedness at a
point of a scheme over a field of positive characteristic.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

noncomputable section

namespace geometricallyReducedAt

/-- A point of a scheme over a field of prime characteristic is geometrically reduced if and
only if every point above it after every finite purely inseparable field extension has a reduced
local ring. -/
@[stacks 035Y]
theorem iff_forall_isReduced_stalk_finitePurelyInseparable
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))
    (p : ℕ) [Fact p.Prime] [CharP k p] (x : X.left) :
    geometricallyReducedAt X x ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [IsPurelyInseparable k k'],
        ∀ x' : FieldExtension.baseChange k k' X.hom,
          FieldExtension.toSource k k' X.hom x' = x →
            _root_.IsReduced ((FieldExtension.baseChange k k' X.hom).presheaf.stalk x') := sorry

/-- A point of a scheme over a field of prime characteristic is geometrically reduced if and
only if every point above it after base change to the first pth-root extension has a reduced
local ring. -/
@[stacks 035Y]
theorem iff_isReduced_stalk_onePthRootExtension
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))
    (p : ℕ) [Fact p.Prime] [CharP k p] (x : X.left) :
    geometricallyReducedAt X x ↔
      ∀ x' : FieldExtension.baseChange k (IntermediateField.onePthRootExtension k p) X.hom,
        FieldExtension.toSource k (IntermediateField.onePthRootExtension k p) X.hom x' = x →
          _root_.IsReduced
            ((FieldExtension.baseChange k
              (IntermediateField.onePthRootExtension k p) X.hom).presheaf.stalk x') := sorry

/-- A point of a scheme over a field of prime characteristic is geometrically reduced if and
only if every point above it after base change to the perfect closure has a reduced local ring. -/
@[stacks 035Y]
theorem iff_isReduced_stalk_perfectClosure
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))
    (p : ℕ) [Fact p.Prime] [CharP k p] (x : X.left) :
    geometricallyReducedAt X x ↔
      ∀ x' : FieldExtension.baseChange k (perfectClosure k (AlgebraicClosure k)) X.hom,
        FieldExtension.toSource k (perfectClosure k (AlgebraicClosure k)) X.hom x' = x →
          _root_.IsReduced
            ((FieldExtension.baseChange k
              (perfectClosure k (AlgebraicClosure k)) X.hom).presheaf.stalk x') := sorry

end geometricallyReducedAt

end

end AlgebraicGeometry.SchemeOverField
