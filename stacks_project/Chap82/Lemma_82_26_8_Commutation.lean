/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Center
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern

/-!
# Commutation of first Chern identity classes

In Situation 82.2.1, the identity class `c₁(L)` of an invertible module on a
good algebraic space `X / B` commutes with every homogeneous class in `A^*(X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowCohomology

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]

/-- The product of homogeneous identity classes in `A^*(X)` is the homogeneous
class of their cap-composition `mulCap`. -/
theorem homogeneous_mulCap {p q : ℤ} (c : degree δ f p) (d : degree δ f q) :
    homogeneous δ f p c * homogeneous δ f q d =
      homogeneous δ f (p + q) (mulCap δ f c d) :=
  sorry

variable (L : X.Modules) [isInvertibleObject L]

/-- The identity class `OperationalFirstChern.degree f δ L` commutes in `A^*(X)`
with every homogeneous class `c ∈ Aᵖ(X)`. -/
theorem firstChernClass_comm (p : ℤ) (c : degree δ f p) :
    homogeneous δ f 1 (OperationalFirstChern.degree f δ L) * homogeneous δ f p c =
      homogeneous δ f p c * homogeneous δ f 1 (OperationalFirstChern.degree f δ L) :=
  sorry

/-- Capping with `OperationalFirstChern.degree f δ L` commutes with capping by a
homogeneous identity class, after reindexing along `k - 1 - p = k - p - 1`. -/
theorem firstChernClass_cap_comm {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (p : ℤ) (c : degree δ f p) (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k) :
    (OperationalFirstChern.degree f δ L).cap g (k - p) (c.cap g k α) =
      castChowGroup δ (g ≫ f) (sub_right_comm k 1 p)
        (c.cap g (k - 1) ((OperationalFirstChern.degree f δ L).cap g k α)) :=
  sorry

/-- The identity class `OperationalFirstChern.ringClass f δ L` lies in the center
of the Chow cohomology ring `A^*(X)`. -/
theorem firstChernClass_mem_center :
    OperationalFirstChern.ringClass f δ L ∈ Set.center (ring δ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChowCohomology
