/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.ProperPushforward

/-! Flat pullback, powers of first Chern intersection, and proper pushforward.
These maps make sense for the displayed geometry. Bijectivity is deliberately
not asserted for an arbitrary flat morphism or arbitrary invertible H.
-/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
open scoped BigOperators
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveFormulaMap

variable {S : Scheme.{u}} {B X P : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (π : P ⟶ X) [QuasiSeparated (π ≫ f)] [LocallyOfFiniteType (π ≫ f)]
    (q : ℕ) [Flat π] [RelativeDimension π q]
    (H : P.Modules) [isInvertibleObject H]

/-- The actual Chow pullback of the given morphism, including fibre multiplicities. -/
def pullback (k : ℤ) : Hom.chowGroup f δ k →+ Hom.chowGroup (π ≫ f) δ (k + q) :=
  AlgebraicGeometry.AlgebraicSpace.ChowGroup.flatPullback f (π ≫ f) δ π q rfl k

/-- The i-th genuine term ξ^i cap π*; the degree transport is arithmetic only. -/
def term (k : ℤ) (i : Fin (q + 1)) :
    Hom.chowGroup f δ (k + i.val) →+ Hom.chowGroup (π ≫ f) δ (k + q) :=
  ((AddEquiv.cast (M := Hom.chowGroup (π ≫ f) δ)
    (show ((k + i.val) + q) - i.val = k + q by omega)).toAddMonoidHom).comp
      ((FirstChernChow.power (π ≫ f) δ H i.val ((k + i.val) + q)).comp
        (pullback f δ π q (k + i.val)))

/-- The sum of first Chern powers after flat pullback, over the degrees indexed by
`Fin (q + 1)`. -/
def formula (k : ℤ) :
    (∀ i : Fin (q + 1), Hom.chowGroup f δ (k + i.val)) →+
      Hom.chowGroup (π ≫ f) δ (k + q) :=
  ∑ i : Fin (q + 1), (term f δ π q H k i).comp
    (Pi.evalAddMonoidHom (fun j : Fin (q + 1) ↦ Hom.chowGroup f δ (k + j.val)) i)

/-- The finite-sum homomorphism evaluates as the sum of its first Chern terms. -/
theorem formula_apply (k : ℤ)
    (a : ∀ i : Fin (q + 1), Hom.chowGroup f δ (k + i.val)) :
    formula f δ π q H k a = ∑ i : Fin (q + 1), term f δ π q H k i (a i) := by
  simp [formula]

/-- Actual Segre-type operation π_* (ξ^(q+j) cap π*(-)), of degree -j.
Its Chern normalization requires H=O(1) on the actual projectivization of E;
no such characterization is assumed for this general map. -/
def segre [Proper π] (j : ℕ) (k : ℤ) :
    Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k - j) :=
  (AlgebraicGeometry.AlgebraicSpace.ChowGroup.properPushforward (π ≫ f) f δ π rfl (k - j)).comp
    (((AddEquiv.cast (M := Hom.chowGroup (π ≫ f) δ)
      (show (k + q) - (q + j : ℕ) = k - j by omega)).toAddMonoidHom).comp
        ((FirstChernChow.power (π ≫ f) δ H (q + j) (k + q)).comp
          (pullback f δ π q k)))

/-- The Segre-type operation evaluates by flat pullback, a first Chern power,
degree transport, and proper pushforward. -/
theorem segre_apply [Proper π] (j : ℕ) (k : ℤ) (a : Hom.chowGroup f δ k) :
    segre f δ π q H j k a =
      AlgebraicGeometry.AlgebraicSpace.ChowGroup.properPushforward (π ≫ f) f δ π rfl (k - j)
        ((AddEquiv.cast (M := Hom.chowGroup (π ≫ f) δ)
          (show (k + q) - (q + j : ℕ) = k - j by omega)).toAddMonoidHom
          (FirstChernChow.power (π ≫ f) δ H (q + j) (k + q)
            (pullback f δ π q k a))) := rfl

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveFormulaMap
