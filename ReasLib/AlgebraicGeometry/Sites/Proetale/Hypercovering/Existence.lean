/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
public import ReasLib.CategoryTheory.Sites.WeaklyContractible

/-!
# Weakly contractible singleton hypercoverings

Every object of the small pro-étale site admits a hypercovering whose degree
families are singletons of weakly contractible objects. If the object is
quasi-compact and quasi-separated, those sources may be taken affine.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every object of the small pro-étale site of `X` admits a hypercovering of
that object whose every degree family is a singleton weakly contractible object. -/
theorem exists_hypercovering_isWeaklyContractibleSingleton
    (X : Scheme.{u}) (U : X.ProEt) :
    ∃ K : Hypercovering.{u} (topology X) U,
      (∀ n, Nonempty (K.family n).index) ∧
        (∀ n, Subsingleton (K.family n).index) ∧
          (∀ n i, (topology X).IsWeaklyContractible ((K.family n).obj i).left) :=
  sorry

/-- Every quasi-compact quasi-separated object of the small pro-étale site of
`X` admits a hypercovering of that object whose every degree family is a
singleton affine weakly contractible object. -/
theorem exists_hypercovering_isAffine_isWeaklyContractibleSingleton
    (X : Scheme.{u}) (U : X.ProEt)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    ∃ K : Hypercovering.{u} (topology X) U,
      (∀ n, Nonempty (K.family n).index) ∧
        (∀ n, Subsingleton (K.family n).index) ∧
          (∀ n i,
            IsAffine ((K.family n).obj i).left.left ∧
              (topology X).IsWeaklyContractible ((K.family n).obj i).left) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
