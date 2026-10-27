/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowCohomology.Operational
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Fundamental

/-! # Vanishing of operational Chow classes -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (δ : Points B → ℤ) [IsDimensionFunction δ]
  (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]

namespace OperationalChow

/-- An operational Chow class vanishes when every cap map in its family is
the zero homomorphism. -/
def Vanishes {p : ℤ} (c : OperationalChow δ f p) : Prop :=
  ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
    c.cap g k = 0

/-- The zero operational Chow class has zero cap action on every test space. -/
theorem vanishes_zero (p : ℤ) : Vanishes δ f (zero δ f p) :=
  sorry

/-- An operational Chow class equals zero exactly when all its cap maps vanish. -/
theorem eq_zero_iff_vanishes {p : ℤ} (c : OperationalChow δ f p) :
    c = zero δ f p ↔ Vanishes δ f c :=
  sorry

/-- The cap of an operational Chow class with an integral fundamental class. -/
def cap_fundamental {Y : AlgebraicSpace S} {p : ℤ} (c : OperationalChow δ f p)
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    [IsIntegral Y] :
    Hom.chowGroup (g ≫ f) δ
      (Hom.deltaDimension (g ≫ f) δ (univIrreducibleClosed Y) - p) :=
  c.cap g (Hom.deltaDimension (g ≫ f) δ (univIrreducibleClosed Y))
    (Hom.integralFundamentalClass (g ≫ f) δ)

/-- The cap operation is definitionally evaluation on the fundamental class. -/
theorem cap_fundamental_eq {Y : AlgebraicSpace S} {p : ℤ}
    (c : OperationalChow δ f p) (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    [IsIntegral Y] :
    cap_fundamental δ f c g =
      c.cap g (Hom.deltaDimension (g ≫ f) δ (univIrreducibleClosed Y))
        (Hom.integralFundamentalClass (g ≫ f) δ) := rfl

/-- An operational Chow class is zero exactly when it caps to zero on every
integral locally-of-finite-type test space. -/
theorem eq_zero_iff_cap_fundamental {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (p : ℤ)
    (c : OperationalChow δ f p) :
    c = zero δ f p ↔
      ∀ (Y : AlgebraicSpace S) (g : Y ⟶ X)
        [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
        [LocallyOfFiniteType g] [IsIntegral Y],
        cap_fundamental δ f c g = 0 :=
  sorry

end OperationalChow

end AlgebraicGeometry.AlgebraicSpace
