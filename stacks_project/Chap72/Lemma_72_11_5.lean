/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Reduced.Criteria
import StacksCheckRecall

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

universe u

/- Lemma 72.11.5: let `k` be a field of characteristic `p > 0` and let `X` be an
algebraic space over `k`. The following are equivalent: `X` is geometrically
reduced over `k`; `baseChange (specMap k k') X` is reduced for every field
extension `k'/k`; the same for every finite purely inseparable extension
`k'/k`; `baseChange (specMap k (IntermediateField.onePthRootExtension k p)) X`
is reduced; `baseChange (specMap k (kᵖᵉʳᶠ)) X` is reduced; and
`baseChange (specMap k (AlgebraicClosure k)) X` is reduced. -/
@[stacks 0E03] #check
  (AlgebraicGeometry.AlgebraicSpace.geometricallyReduced_tfae :
    ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
      [CharP k p] (X : AlgebraicSpace (Spec (CommRingCat.of k))),
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
        IsReduced (baseChange (specMap k (AlgebraicClosure k)) X)])

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyReduced.iff :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (CommRingCat.of k))),
    GeometricallyReduced X ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k'],
        IsReduced (baseChange (specMap k k') X))
