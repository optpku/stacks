/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Grassmannian.Representability
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/-- The Grassmannian functor classifying rank-`n - k` finite locally free quotients of the
free rank-`n` module sheaf. -/
noncomputable abbrev G (k n : ℕ) : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type (u + 1) :=
  AlgebraicGeometry.Grassmannian.functor k n

/-- For `0 < k < n`, the Grassmannian functor `G k n` is representable. -/
theorem grassmannianFunctor_isRepresentable (k n : ℕ) (hk : 0 < k) (hkn : k < n) :
    CategoryTheory.Functor.IsRepresentable (G.{u} k n) :=
  AlgebraicGeometry.Grassmannian.functor_isRepresentable k n hk hkn

/- Lemma 27.22.1: for natural numbers `0 < k < n`, the Grassmannian functor `G(k, n)` is
representable by a scheme. -/
@[stacks 089T] #check (AlgebraicGeometry.Grassmannian.functor_isRepresentable :
  ∀ (k n : ℕ), 0 < k → k < n →
    CategoryTheory.Functor.IsRepresentable
      (AlgebraicGeometry.Grassmannian.functor.{u} k n))
