/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow

/-! # Powers of degree-one cap families -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowCohomology

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable {δ : Points B → ℤ} [IsDimensionFunction δ]
variable {f : X ⟶ B} [QuasiSeparated f] [LocallyOfFiniteType f]

/-- Zero-fold iteration is the identity cap family, reindexed along `k - 0 = k`. -/
def powCapZero :
    ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - 0) :=
  fun {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ) (sub_zero k).symm).toAddMonoidHom

variable (c : ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
  [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
  Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - 1))

/-- The successor stage composes a degree-one cap with a degree-`j` cap family. -/
def powCapSucc (j : ℕ)
    (ih : ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - j)) :
    ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - (j + 1 : ℕ)) :=
  fun {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    ((AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ)
      (show (k - (j : ℤ)) - 1 = k - ((j + 1 : ℕ) : ℤ) by omega)).toAddMonoidHom).comp
      ((c g (k - (j : ℤ))).comp (ih g k))

/-- The natural-number powers of a degree-one additive cap family. -/
def powCap : (j : ℕ) →
    ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - j) :=
  Nat.rec powCapZero (fun j ih ↦ powCapSucc c j ih)

/-- The zeroth power is the identity with its degree reindexing. -/
theorem powCap_zero {Y : AlgebraicSpace S}
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    powCap c 0 g k =
      (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ) (sub_zero k).symm).toAddMonoidHom :=
  rfl

/-- The successor power applies the degree-one cap after the preceding power. -/
theorem powCap_succ (j : ℕ)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    powCap c (j + 1) g k =
      ((AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ)
        (show (k - (j : ℤ)) - 1 = k - ((j + 1 : ℕ) : ℤ) by omega)).toAddMonoidHom).comp
        ((c g (k - (j : ℤ))).comp (powCap c j g k)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.ChowCohomology
