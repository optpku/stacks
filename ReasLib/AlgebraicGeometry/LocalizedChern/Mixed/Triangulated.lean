/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.EnvelopeClasses
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Triangulated.Connecting
public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.MixedProduct

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open BivariantClass.Cutoff ChernClass.Derived
open ChowCohomology.Nonnegative.Completion
open RingedSpace.ModuleDerived.Morphism

/-- In a distinguished triangle whose first and third restrictions away from a
closed center are degree-zero vector bundles of ranks strictly below `p1` and
`p3`, the middle restriction is a degree-zero vector bundle of rank strictly
below `p1 + p3`. -/
theorem rankBound_obj₂
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (p1 p3 : ℕ)
    (rank1 : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i T.obj₁) 0 p1)
    (rank3 : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i T.obj₃) 0 p3) :
    Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i T.obj₂) 0 (p1 + p3) := sorry

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable {δ : S → ℤ} [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
variable (i : Z ⟶ X.left) [IsClosedImmersion i]
variable (T : Triangle (RingedSpace.ModuleDerived X.left.toRingedSpace))
variable (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.left.toRingedSpace))
variable (h1 : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
variable (h2 : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
variable (h3 : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
variable (p1 p3 : ℕ)
variable (rank1 : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
    (restrictAway i T.obj₁) 0 p1)
variable (rank3 : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
    (restrictAway i T.obj₃) 0 p3)
variable (hfin :
    (∃ (Y : Scheme.{u}) (f : Y ⟶ X.left), IsEnvelope f ∧
      HasLocallyBoundedFiniteLocallyFree
        ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₃)) ∨
    HasLocallyBoundedFiniteLocallyFree T.mor₃ ∨
    (∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) ∨
    CompactSpace X.left)
variable (classes : ChernClass.Theory δ X.hom)

/-- The full mixed localized Chern family is multiplicative on a distinguished
triangle of perfect objects under the off-center rank bounds and the four
connecting-map representability or compactness alternatives. -/
theorem mixedChernClass_distinguished_family :
    EnvelopeClasses.mixedChernClass i classes T.obj₂ h2
      (isDefined_obj₂_of_connecting
          (noetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom) T hT h1 h2 h3 hfin)
      (p1 + p3) (rankBound_obj₂ i T hT p1 p3 rank1 rank3) =
      BivariantClass.Cutoff.familyMul δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p1 p3
        (EnvelopeClasses.mixedChernClass i classes T.obj₁ h1
          (isDefined_obj₁_of_connecting
          (noetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom) T hT h1 h2 h3 hfin) p1 rank1)
        (EnvelopeClasses.mixedChernClass i classes T.obj₃ h3
          (isDefined_obj₃_of_connecting
          (noetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom) T hT h1 h2 h3 hfin) p3 rank3) := sorry

/-- Below the sum cutoff, the middle mixed Chern coefficient is the ambient
Cauchy product of the total Chern classes of the outer vertices. -/
theorem mixedChernClass_distinguished_lt (n : ℕ) (hn : n < p1 + p3) :
    EnvelopeClasses.mixedChernClass i classes T.obj₂ h2
      (isDefined_obj₂_of_connecting
          (noetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom) T hT h1 h2 h3 hfin)
      (p1 + p3) (rankBound_obj₂ i T hT p1 p3 rank1 rank3) n =
      ofAmbient δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (Nat.cast_lt.mpr hn)
        (mul δ X.hom
          (totalClass δ X.hom classes T.obj₁ h1
            (isDefined_obj₁_of_connecting
          (noetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom) T hT h1 h2 h3 hfin))
          (totalClass δ X.hom classes T.obj₃ h3
            (isDefined_obj₃_of_connecting
          (noetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom) T hT h1 h2 h3 hfin)) n) := sorry

/-- From the sum cutoff onward, the middle mixed Chern coefficient is the
relative mixed Cauchy product of the outer mixed Chern families. -/
theorem mixedChernClass_distinguished (n : ℕ) (hn : p1 + p3 ≤ n) :
    EnvelopeClasses.mixedChernClass i classes T.obj₂ h2
      (isDefined_obj₂_of_connecting
          (noetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom) T hT h1 h2 h3 hfin)
      (p1 + p3) (rankBound_obj₂ i T hT p1 p3 rank1 rank3) n =
      ofRelative δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
        (not_lt.mpr (Nat.cast_le.mpr hn))
        (mixedMul δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p1 p3 n hn
          (EnvelopeClasses.mixedChernClass i classes T.obj₁ h1
          (isDefined_obj₁_of_connecting
          (noetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom) T hT h1 h2 h3 hfin) p1 rank1)
          (EnvelopeClasses.mixedChernClass i classes T.obj₃ h3
          (isDefined_obj₃_of_connecting
          (noetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom) T hT h1 h2 h3 hfin) p3 rank3)) := sorry

end AlgebraicGeometry.LocalizedChern
