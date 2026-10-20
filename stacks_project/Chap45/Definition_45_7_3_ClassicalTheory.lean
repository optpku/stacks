module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical

@[expose] public section

open CategoryTheory

universe u v w x y z

/- The compatibility module exports the complete classical Weil cohomology interface. -/
#check (WeilCohomology.ClassicalTheory :
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
