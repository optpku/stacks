/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Grassmannian.Representability

/-!
# Explicit models of the Grassmannian functor

A model records a representing scheme and its universal point as explicit data.

Stacks Tag `089T` proves representability by gluing the subfunctors indexed by the
`(n - k)`-element subsets of `{1, ..., n}`. Each is represented by
`A^{k(n-k)}_ℤ`; Tag `089U` then names a scheme representing the functor, without
specifying a particular choice of gluing data. `Model` is the interface for any
such realization together with its universal point, hence for a representing
object up to the unique isomorphism preserving that point. It does not implement
the affine charts or their gluing. In particular, `model_nonempty` is only an
existence assertion, and is not used to choose scheme data for base change.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Grassmannian

/-- An explicit representing model of the Grassmannian functor for indices `0 < k < n`. -/
structure Model (k n : ℕ) (hk : 0 < k) (hkn : k < n) where
  /-- The scheme underlying the representing model. -/
  scheme : Scheme.{u}
  /-- The universal Grassmannian point carried by the model. -/
  point : (functor k n).obj (Opposite.op scheme)
  /-- The stored point represents the Grassmannian functor. -/
  isRepresentedBy : (functor k n).IsRepresentedBy point

namespace Model

/-- Construct a Grassmannian model from an explicit scheme, point, and representability law. -/
def ofPoint {k n : ℕ} (hk : 0 < k) (hkn : k < n) (X : Scheme.{u})
    (x : (functor k n).obj (Opposite.op X))
    (hx : (functor k n).IsRepresentedBy x) : Model k n hk hkn where
  scheme := X
  point := x
  isRepresentedBy := hx

end Model

/-- A representing model of the Grassmannian functor exists for indices `0 < k < n`. -/
theorem model_nonempty (k n : ℕ) (hk : 0 < k) (hkn : k < n) :
    Nonempty (Model.{u} k n hk hkn) := by
  letI := functor_isRepresentable k n hk hkn
  exact ⟨Model.ofPoint hk hkn (functor k n).reprX (functor k n).reprx
    CategoryTheory.Functor.IsRepresentedBy.of_isRepresentable⟩

end AlgebraicGeometry.Grassmannian
