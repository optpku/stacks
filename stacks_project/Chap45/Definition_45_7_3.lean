/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical
import StacksCheckRecall

open CategoryTheory

universe u v w x y z

/- Definition 45.7.3: for an algebraically closed field `k` and a characteristic-zero
field `F`, a classical Weil cohomology theory consists of data (D1), (D2), and (D3)
satisfying Poincaré duality (A), the Künneth formula (B), and compatibility with
cycle classes (C). -/
@[stacks 0FGV] #check (WeilCohomology.ClassicalTheory :
  (k : Type u) → [Field k] → [IsAlgClosed k] →
  (F : Type v) → [Field F] → [CharZero F] →
  (V : Type w) → [Category.{z} V] →
  (dimension : V → ℕ) → (product : V → V → V) →
  (fst : (X Y : V) → product X Y ⟶ X) →
  (snd : (X Y : V) → product X Y ⟶ Y) →
  (point : V) → (H : V → Type x) → (CH : V → Type y) →
  [(X : V) → Ring (H X)] → [(X : V) → Algebra F (H X)] →
  [(X : V) → CommRing (CH X)] →
  (Hgrade : (X : V) → ℤ → Submodule F (H X)) →
  (CHgrade : (X : V) → ℤ → Submodule ℤ (CH X)) →
  [(X : V) → GradedAlgebra (Hgrade X)] →
  [(X : V) → GradedAlgebra (CHgrade X)] →
  (cyclePullback : {X Y : V} → (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X) →
  (cyclePushforward : {X Y : V} → (X ⟶ Y) → CH X →+ CH Y) →
  (pointCycle : CHgrade point 0) →
  Type (max (max (max (max (max (u + 1) v) w) x) y) z))
