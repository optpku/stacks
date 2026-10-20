/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.FieldTheory.PurelyInseparable.OnePthRoot
public import ReasLib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# Criteria for geometrically reduced algebraic spaces

For an algebraic space over a field of positive characteristic, geometric reducedness
can be tested after finite purely inseparable extensions, the first Frobenius-root
extension, the perfect closure, or an algebraic closure.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CommRingCat
open AlgebraicGeometry.FieldExtension (specMap)
open scoped PerfectClosure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For an algebraic space over a field of positive characteristic, geometric reducedness
is equivalent to reducedness after every field extension, after every finite purely
inseparable extension, and after base change to the first Frobenius-root extension,
the perfect closure, or an algebraic closure. -/
@[stacks 0E03]
theorem geometricallyReduced_tfae {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    List.TFAE
      [GeometricallyReduced X,
        ∀ (k' : Type u) [Field k'] [Algebra k k'],
          IsReduced (baseChange (specMap k k') X),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [IsPurelyInseparable k k'],
          IsReduced (baseChange (specMap k k') X),
        IsReduced
          (baseChange (specMap k (IntermediateField.onePthRootExtension k p)) X),
        IsReduced (baseChange (specMap k (kᵖᵉʳᶠ)) X),
        IsReduced (baseChange (specMap k (AlgebraicClosure k)) X)] :=
  sorry

namespace GeometricallyReduced

/-- An algebraic space over a field of characteristic `p > 0` is geometrically
reduced if and only if its base change along `specMap k k'` is reduced for every
finite purely inseparable field extension `k'/k`. -/
theorem iff_isReduced_forall_finitePurelyInseparable {k : Type u} [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    GeometricallyReduced X ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsReduced (baseChange (specMap k k') X) :=
  (geometricallyReduced_tfae p X).out 0 2

/-- An algebraic space over a field of characteristic `p > 0` is geometrically
reduced if and only if its base change to `IntermediateField.onePthRootExtension k p`
is reduced. -/
theorem iff_isReduced_onePthRootExtension {k : Type u} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    GeometricallyReduced X ↔
      IsReduced
        (baseChange (specMap k (IntermediateField.onePthRootExtension k p)) X) :=
  (geometricallyReduced_tfae p X).out 0 3

/-- An algebraic space over a field of characteristic `p > 0` is geometrically
reduced if and only if its base change to `kᵖᵉʳᶠ` is reduced. -/
theorem iff_isReduced_perfectClosure {k : Type u} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    GeometricallyReduced X ↔
      IsReduced (baseChange (specMap k (kᵖᵉʳᶠ)) X) :=
  (geometricallyReduced_tfae p X).out 0 4

/-- An algebraic space over a field of characteristic `p > 0` is geometrically
reduced if and only if its base change to `AlgebraicClosure k` is reduced. -/
theorem iff_isReduced_algebraicClosure {k : Type u} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    GeometricallyReduced X ↔
      IsReduced (baseChange (specMap k (AlgebraicClosure k)) X) :=
  (geometricallyReduced_tfae p X).out 0 5

end GeometricallyReduced

end AlgebraicGeometry.AlgebraicSpace
