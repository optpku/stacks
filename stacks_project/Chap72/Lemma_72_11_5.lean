module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.FieldTheory.PurelyInseparable.OnePthRoot
public import ReasLib.FieldTheory.PurelyInseparable.PerfectClosure
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap72.Definition_72_11_1_GeometricallyReduced

/-!
# Geometric reducedness in positive characteristic

For an algebraic space over a field of characteristic `p > 0`, geometric
reducedness is equivalent to reducedness after every field extension, after
every finite purely inseparable extension, and after base change to the first
Frobenius-root extension, the perfect closure, or an algebraic closure.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CommRingCat
open AlgebraicGeometry.FieldExtension (specMap)
open scoped PerfectClosure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.11.5: let `k` be a field of characteristic `p > 0` and let `X` be an
algebraic space over `k`. The following are equivalent: `X` is geometrically
reduced over `k`; `baseChange (specMap k k') X` is reduced for every field
extension `k'/k`; the same for every finite purely inseparable extension
`k'/k`; `baseChange (specMap k (IntermediateField.onePthRootExtension k p)) X`
is reduced; `baseChange (specMap k (kᵖᵉʳᶠ)) X` is reduced; and
`baseChange (specMap k (AlgebraicClosure k)) X` is reduced. -/
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
field extension `k'/k`. -/
theorem iff_isReduced_forall_fieldExtension {k : Type u} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    GeometricallyReduced X ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k'],
        IsReduced (baseChange (specMap k k') X) :=
  sorry

/-- An algebraic space over a field of characteristic `p > 0` is geometrically
reduced if and only if its base change along `specMap k k'` is reduced for every
finite purely inseparable field extension `k'/k`. -/
theorem iff_isReduced_forall_finitePurelyInseparable {k : Type u} [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    GeometricallyReduced X ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsReduced (baseChange (specMap k k') X) :=
  sorry

/-- An algebraic space over a field of characteristic `p > 0` is geometrically
reduced if and only if its base change to `IntermediateField.onePthRootExtension k p`
is reduced. -/
theorem iff_isReduced_onePthRootExtension {k : Type u} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    GeometricallyReduced X ↔
      IsReduced
        (baseChange (specMap k (IntermediateField.onePthRootExtension k p)) X) :=
  sorry

/-- An algebraic space over a field of characteristic `p > 0` is geometrically
reduced if and only if its base change to `kᵖᵉʳᶠ` is reduced. -/
theorem iff_isReduced_perfectClosure {k : Type u} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    GeometricallyReduced X ↔
      IsReduced (baseChange (specMap k (kᵖᵉʳᶠ)) X) :=
  sorry

/-- An algebraic space over a field of characteristic `p > 0` is geometrically
reduced if and only if its base change to `AlgebraicClosure k` is reduced. -/
theorem iff_isReduced_algebraicClosure {k : Type u} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    GeometricallyReduced X ↔
      IsReduced (baseChange (specMap k (AlgebraicClosure k)) X) :=
  sorry

end GeometricallyReduced

end AlgebraicGeometry.AlgebraicSpace
