/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Grassmannian.Model

/-!
# Grassmannians over a base scheme

An explicit integral Grassmannian model can be pulled back to any scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Grassmannian

/-- The base change of an explicit Grassmannian model to a scheme `S`. -/
def baseChange {k n : ℕ} {hk : 0 < k} {hkn : k < n}
    (P : Model.{u} k n hk hkn) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from P.scheme)

/-- The canonical projection from a base-changed Grassmannian to its base scheme. -/
def toBase {k n : ℕ} {hk : 0 < k} {hkn : k < n}
    (P : Model.{u} k n hk hkn) (S : Scheme.{u}) :
    baseChange P S ⟶ S :=
  pullback.fst _ _

/-- The Grassmannian over a commutative ring is the base change to its spectrum. -/
def overRing {k n : ℕ} {hk : 0 < k} {hkn : k < n}
    (P : Model.{u} k n hk hkn) (R : Type u) [CommRing R] : Scheme.{u} :=
  baseChange P (AlgebraicGeometry.Spec (.of R))

end AlgebraicGeometry.Grassmannian
