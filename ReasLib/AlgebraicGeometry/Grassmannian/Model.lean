/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Grassmannian.Representability

/-!
# Explicit models of the Grassmannian functor

A model records a representing scheme and its universal point as explicit data.
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
    Nonempty (Model.{u} k n hk hkn) := sorry

end AlgebraicGeometry.Grassmannian
