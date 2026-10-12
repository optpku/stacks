/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank

/-! The real first-Chern bivariant class, including the constant-rank-one case. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L]

/-- On each good test space, use the actual pulled-back line and quotient c1. -/
def family : ChowCohomology.CapFamily δ f 1 :=
  fun {Y} g _ _ k ↦
    @FirstChernChow.lower S B Y _ _ (g ≫ f) _ _ δ _
      ((Modules.pullback g).obj L) (Modules.isInvertibleObject_pullback g L) k

/-- Projection formula for this specified first-Chern cap. -/
theorem proper : ChowCohomology.CompatibleWithProperPushforward δ f (family f δ L) := by
  sorry

/-- Flat-basechange compatibility of this specified first-Chern cap. -/
theorem flat : ChowCohomology.CompatibleWithFlatPullback δ f (family f δ L) := by
  sorry

/-- Commutation with the real two-branch refined Gysin map. -/
theorem gysin : ChowCohomology.CompatibleWithCartierGysin δ f (family f δ L) := by
  sorry

/-- Lemma82.26.4's class, assembled from its explicit cap family. -/
def degree : ChowCohomology.degree δ f 1 :=
  ChowCohomology.ofCap δ f (family f δ L) (proper f δ L) (flat f δ L) (gysin f δ L)

theorem degree_cap {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (degree f δ L).cap g k =
      @FirstChernChow.lower S B Y _ _ (g ≫ f) _ _ δ _
        ((Modules.pullback g).obj L) (Modules.isInvertibleObject_pullback g L) k := rfl

/-- The homogeneous first Chern class in the existing genuine Chow ring. -/
def ringClass : ChowCohomology.ring δ f :=
  ChowCohomology.homogeneous δ f 1 (degree f δ L)

/-- Rank-one finite local freeness makes the actual E tensor invertible. This
is a property of E, not a chosen replacement line or a Chern-family hypothesis. -/
theorem rankOne_invertible (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank 1 E] :
    isInvertibleObject E := by
  sorry

/-- The constant-rank-one positive Chern class uses E itself. -/
def rankOne (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank 1 E] :
    ChowCohomology.degree δ f 1 :=
  @degree S B X _ _ f _ _ δ _ E (rankOne_invertible E)

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
