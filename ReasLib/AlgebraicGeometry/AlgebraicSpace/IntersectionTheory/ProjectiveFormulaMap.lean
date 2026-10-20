module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow

/-! Actual maps needed by 82.27: flat pullback, powers of c1, and proper pushforward.
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
  chowFlatPullback δ f (π ≫ f) π q rfl k

/-- The i-th genuine term ξ^i cap π*; the degree transport is arithmetic only. -/
def term (k : ℤ) (i : Fin (q + 1)) :
    Hom.chowGroup f δ (k + i.val) →+ Hom.chowGroup (π ≫ f) δ (k + q) :=
  (ChowCohomology.castChowGroup δ (π ≫ f)
    (show ((k + i.val) + q) - i.val = k + q by omega)).comp
      ((FirstChernChow.power (π ≫ f) δ H i.val ((k + i.val) + q)).comp
        (pullback f δ π q (k + i.val)))

/-- The exact finite-sum map in 82.27.2 for positive rank r=q+1. -/
def formula (k : ℤ) :
    (∀ i : Fin (q + 1), Hom.chowGroup f δ (k + i.val)) →+
      Hom.chowGroup (π ≫ f) δ (k + q) :=
  ∑ i : Fin (q + 1), (term f δ π q H k i).comp
    (Pi.evalAddMonoidHom (fun j : Fin (q + 1) ↦ Hom.chowGroup f δ (k + j.val)) i)

theorem formula_apply (k : ℤ)
    (a : ∀ i : Fin (q + 1), Hom.chowGroup f δ (k + i.val)) :
    formula f δ π q H k a = ∑ i : Fin (q + 1), term f δ π q H k i (a i) := by
  simp [formula]

/-- Actual Segre-type operation π_* (ξ^(q+j) cap π*(-)), of degree -j.
Its Chern normalization requires H=O(1) on the actual projectivization of E;
no such characterization is assumed for this general map. -/
def segre [Proper π] (j : ℕ) (k : ℤ) :
    Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k - j) :=
  (properPushforward δ (π ≫ f) f π rfl (k - j)).comp
    ((ChowCohomology.castChowGroup δ (π ≫ f)
      (show (k + q) - (q + j : ℕ) = k - j by omega)).comp
        ((FirstChernChow.power (π ≫ f) δ H (q + j) (k + q)).comp
          (pullback f δ π q k)))

theorem segre_apply [Proper π] (j : ℕ) (k : ℤ) (a : Hom.chowGroup f δ k) :
    segre f δ π q H j k a =
      properPushforward δ (π ≫ f) f π rfl (k - j)
        (ChowCohomology.castChowGroup δ (π ≫ f)
          (show (k + q) - (q + j : ℕ) = k - j by omega)
          (FirstChernChow.power (π ≫ f) δ H (q + j) (k + q)
            (pullback f δ π q k a))) := rfl

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveFormulaMap
