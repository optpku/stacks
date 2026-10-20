/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.PurelyInseparable

@[expose] public section

open AddSubgroup

universe u

/- Lemma 44.7.2: for a quasi-compact and quasi-separated scheme `X` over a field `k` of
positive characteristic `p`, with `k ≃ Γ(X, 𝒪_X)`, purely inseparable extension of scalars
bijects the `n`-torsion Picard classes whenever `n` is prime to `p`. -/
@[stacks 0CD5] #check
  (AlgebraicGeometry.FieldExtension.picardPullback_bijOn_torsionBy :
    ∀ (p : ℕ) [Fact p.Prime] {k k' : Type u}
      [Field k] [CharP k p] [Field k'] [Algebra k k'] [IsPurelyInseparable k k']
      (X : AlgebraicGeometry.SchemeOverField k) [CompactSpace X.left.carrier]
      [QuasiSeparatedSpace X.left.carrier]
      (hΓ : Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom))
      (n : ℤ) (h_n : IsCoprime n (p : ℤ)),
      Set.BijOn
        (AlgebraicGeometry.Scheme.Hom.picardPullback
          (AlgebraicGeometry.FieldExtension.toSource k k' X.hom))
        X.left.PicardGroup[n]
        (AlgebraicGeometry.FieldExtension.baseChange k k' X.hom).PicardGroup[n])
