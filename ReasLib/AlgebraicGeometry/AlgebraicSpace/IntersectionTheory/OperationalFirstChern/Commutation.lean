/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
public import Mathlib.Algebra.Group.Center

/-! # Commutation of operational first Chern classes -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (δ : Points B → ℤ) [IsDimensionFunction δ]
  (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
  (L : X.Modules) [isInvertibleObject L]

/-- The operational first Chern class commutes with every homogeneous operational class. -/
theorem comm (p : ℤ) (c : OperationalChow δ f p) :
    OperationalChow.homogeneous δ f 1 (degree f δ L) * OperationalChow.homogeneous δ f p c =
      OperationalChow.homogeneous δ f p c * OperationalChow.homogeneous δ f 1 (degree f δ L) := sorry

/-- First Chern cap commutes with an arbitrary homogeneous cap action after reindexing degrees. -/
theorem cap_comm {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (p : ℤ) (c : OperationalChow δ f p) (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k) :
    (degree f δ L).cap g (k - p) (c.cap g k α) =
      (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ) (sub_right_comm k 1 p))
        (c.cap g (k - 1) ((degree f δ L).cap g k α)) := sorry

/-- The operational first Chern class belongs to the center of the operational Chow ring. -/
theorem mem_center : ringClass f δ L ∈ Set.center (OperationalChow.ring δ f) := sorry

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
