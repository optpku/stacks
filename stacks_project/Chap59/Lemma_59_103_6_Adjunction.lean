module

public import stacks_project.Chap59.Lemma_59_103_5_Comparison
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive

/-!
# Abelian and derived adjunctions for `a_X`

Abelian direct image `a_{X,*} = ε_{X,*} ⋙ π_{X,*}` at `AddCommGrpCat.{u+1}`, together with the
canonical `D⁺` adjunction `a_X⁻¹ ⊣ Ra_{X,*}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HComparison

/-- Direct image `π_{X,*}` on abelian sheaves along identity-base étale relocalization, at the
topology-comparison coefficient universe. -/
def piPushforward (X : Scheme.{u}) :
    Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (relocalizationFunctor (𝟙 X)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    X.smallEtaleTopology (etaleTopology.over X)

/-- Direct image `π_{X,*}` is sheaf pushforward along identity-base étale relocalization. -/
theorem piPushforward_eq (X : Scheme.{u}) :
    piPushforward X =
      (relocalizationFunctor (𝟙 X)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        X.smallEtaleTopology (etaleTopology.over X) := sorry

/-- Direct image `π_{X,*}` is additive. -/
instance piPushforward_additive (X : Scheme.{u}) : (piPushforward X).Additive :=
  inferInstanceAs
    ((relocalizationFunctor (𝟙 X)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      X.smallEtaleTopology (etaleTopology.over X)).Additive

/-- Sheaf-level adjunction `π_X⁻¹ ⊣ π_{X,*}`. -/
def piAdjunction (X : Scheme.{u}) : piInverseImage X ⊣ piPushforward X :=
  (relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    X.smallEtaleTopology (etaleTopology.over X)

/-- Direct image `a_{X,*}` on abelian sheaves from the big h slice `(Sch/X)_h` to the small
étale site of `X`. -/
def aPushforward (X : Scheme.{u}) :
    Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  comparisonTopologyPushforwardAb etale_le_h X ⋙ piPushforward X

/-- Direct image `a_{X,*}` is the composite `ε_{X,*} ⋙ π_{X,*}`. -/
theorem aPushforward_eq (X : Scheme.{u}) :
    aPushforward X = comparisonTopologyPushforwardAb etale_le_h X ⋙ piPushforward X :=
  sorry

/-- Direct image `a_{X,*}` is additive. -/
instance aPushforward_additive (X : Scheme.{u}) : (aPushforward X).Additive :=
  inferInstanceAs
    ((comparisonTopologyPushforwardAb etale_le_h X ⋙ piPushforward X).Additive)

/-- Sheaf-level adjunction `a_X⁻¹ ⊣ a_{X,*}`. -/
def aAdjunction (X : Scheme.{u}) : aInverseImage X ⊣ aPushforward X :=
  (piAdjunction X).comp
    (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_h X)

/-- Sheaf-level `a_X⁻¹ ⊣ a_{X,*}` is the composite of `π_X⁻¹ ⊣ π_{X,*}` with
`ε_X⁻¹ ⊣ ε_{X,*}`. -/
theorem aAdjunction_eq (X : Scheme.{u}) :
    aAdjunction X =
      (piAdjunction X).comp
        (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_h X) := sorry

/-- The bounded-below right-derived functor of `a_{X,*}` exists. -/
instance aPushforward_hasRightDerivedFunctor (X : Scheme.{u}) :
    (aPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1})) := sorry

/-- Bounded-below derived direct image `Ra_{X,*}` on `D⁺`. -/
def plusAPushforward (X : Scheme.{u}) :
    DerivedCategory.Plus
      (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.right (aPushforward X)

/-- Derived direct image `Ra_{X,*}` is the bounded-below right-derived functor of abelian
`a_{X,*}`. -/
theorem plusAPushforward_eq (X : Scheme.{u}) :
    plusAPushforward X = Adjunction.Derived.Plus.right (aPushforward X) := sorry

/-- Bounded-below derived adjunction `a_X⁻¹ ⊣ Ra_{X,*}` on `D⁺`. -/
def plusAAdjunction (X : Scheme.{u}) :
    plusAInverseImage X ⊣ plusAPushforward X :=
  Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseImage X))
    (aPushforward X) (aAdjunction X)

/-- The `D⁺` adjunction `a_X⁻¹ ⊣ Ra_{X,*}` is the exact-left bounded-below derived adjunction of
abelian `a_X⁻¹ ⊣ a_{X,*}`. -/
theorem plusAAdjunction_eq (X : Scheme.{u}) :
    plusAAdjunction X =
      Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseImage X))
        (aPushforward X) (aAdjunction X) := sorry

/-- The sheaf-level adjunction unit of `a_X⁻¹ ⊣ a_{X,*}` is an isomorphism on locally torsion
abelian sheaves. -/
theorem aAdjunction_unit_isIso {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) :
    IsIso ((aAdjunction X).unit.app F) := sorry

/-- Higher direct images `R^q a_{X,*} (a_X⁻¹ F)` vanish for `0 < q` on locally torsion abelian
sheaves. -/
theorem aPushforward_rightDerived_aInverseImage_isZero {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (q : ℕ) (hq : 0 < q) :
    IsZero
      (((aPushforward X).rightDerived q).obj ((aInverseImage X).obj F)) := sorry


end AlgebraicGeometry.Scheme.HComparison

end

end
