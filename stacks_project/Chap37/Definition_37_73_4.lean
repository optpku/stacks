/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification
import StacksCheckRecall

universe u

/- Definition 37.73.4: the affine stratification number is the least length of a finite affine
stratification of a nonempty quasi-compact quasi-separated scheme; equivalently, the least `n`
for which such a stratification has ordered index `Fin (n + 1)`. -/
@[stacks 0F2V] #check (AlgebraicGeometry.Scheme.FiniteAffineStratification.number :
  (X : AlgebraicGeometry.Scheme.{u}) → [Nonempty X] → [CompactSpace X] →
    [QuasiSeparatedSpace X] → ℕ)

#check (AlgebraicGeometry.Scheme.FiniteAffineStratification.number_isLeast :
  ∀ (X : AlgebraicGeometry.Scheme.{u}), [Nonempty X] → [CompactSpace X] →
    [QuasiSeparatedSpace X] →
      IsLeast
        {n | AlgebraicGeometry.Scheme.FiniteAffineStratification.HasLength X n}
        (AlgebraicGeometry.Scheme.FiniteAffineStratification.number X))

#check (AlgebraicGeometry.Scheme.FiniteAffineStratification.hasLength_iff_hasFinIndex :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ),
    AlgebraicGeometry.Scheme.FiniteAffineStratification.HasLength X n ↔
      AlgebraicGeometry.Scheme.FiniteAffineStratification.HasFinIndex X n)
