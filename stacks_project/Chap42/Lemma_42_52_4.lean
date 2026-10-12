/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Remark_42_52_3_CutoffChern
public import stacks_project.Chap42.Lemma_42_46_7
public import stacks_project.Chap42.Lemma_42_47_8_Cutoff

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open BivariantClass.Cutoff
open ChernClass.Derived
open ChowCohomology.Nonnegative.Completion
open RingedSpace.ModuleDerived.Morphism

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable {δ : S → ℤ} [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom]
variable {Z : Scheme.{u}}
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
    (∃ (Y : Scheme.{u}) (f : Y ⟶ X.left),
        IsEnvelope f ∧
          HasLocallyBoundedFiniteLocallyFree
            ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₃)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₃ ∨
      (∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) ∨
      CompactSpace X.left)

include hT h1 h2 h3 p1 p3 rank1 rank3 hfin

/-- Under the four connecting-map alternatives on `T.mor₃`, the derived Chern
classes of `T.obj₁` are defined. -/
theorem isDefined_obj₁ : IsDefined T.obj₁ := sorry

/-- Under the four connecting-map alternatives on `T.mor₃`, the derived Chern
classes of `T.obj₂` are defined. -/
theorem isDefined_obj₂ : IsDefined T.obj₂ := sorry

/-- Under the four connecting-map alternatives on `T.mor₃`, the derived Chern
classes of `T.obj₃` are defined. -/
theorem isDefined_obj₃ : IsDefined T.obj₃ := sorry

/-- The source rank bounds on `T.obj₁` and `T.obj₃` imply that the restriction of
`T.obj₂` away from `Z` is a degree-zero finite locally free module of rank
strictly less than `p1 + p3`. -/
theorem rankBound_obj₂ :
    Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i T.obj₂) 0 (p1 + p3) := sorry

/-- Lemma 42.52.4 (1): in degrees `n < p1 + p3`, the mixed Chern series of
`T.obj₂` equals the ambient Cauchy product of the total Chern classes of
`T.obj₁` and `T.obj₃`. -/
@[stacks 0FBD]
theorem mixedChernClass_distinguished_lt
    (situation₁ : Situation S δ X i T.obj₁ p1 .rankBound)
    (situation₃ : Situation S δ X i T.obj₃ p3 .rankBound)
    (situation₂ : Situation S δ X i T.obj₂ (p1 + p3) .rankBound)
    (classes : ChernClass.Theory δ X.hom) (n : ℕ) (hn : n < p1 + p3) :
    mixedChernClass i classes T.obj₂ (p1 + p3) situation₂ n =
      ofAmbient δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (Nat.cast_lt.mpr hn)
        (mul δ X.hom
          (totalClass δ X.hom classes T.obj₁ h1 (Situation.isDefined situation₁))
          (totalClass δ X.hom classes T.obj₃ h3 (Situation.isDefined situation₃))
          n) :=
  sorry

/-- Lemma 42.52.4 (2): in degrees `p1 + p3 ≤ n`, the mixed Chern series of
`T.obj₂` equals the mixed Cauchy product of the mixed series of `T.obj₁` and
`T.obj₃` as a relative class of cutoff `p1 + p3`. -/
@[stacks 0FBD]
theorem mixedChernClass_distinguished
    (situation₁ : Situation S δ X i T.obj₁ p1 .rankBound)
    (situation₃ : Situation S δ X i T.obj₃ p3 .rankBound)
    (situation₂ : Situation S δ X i T.obj₂ (p1 + p3) .rankBound)
    (classes : ChernClass.Theory δ X.hom) (n : ℕ) (hn : p1 + p3 ≤ n) :
    mixedChernClass i classes T.obj₂ (p1 + p3) situation₂ n =
      ofRelative δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
        (not_lt.mpr (Nat.cast_le.mpr hn))
        (mixedMul δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p1 p3 n hn
          (mixedChernClass i classes T.obj₁ p1 situation₁)
          (mixedChernClass i classes T.obj₃ p3 situation₃)) :=
  sorry

end AlgebraicGeometry.LocalizedChern
