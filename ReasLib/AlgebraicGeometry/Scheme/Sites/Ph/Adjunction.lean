module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.DerivedComparison

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

namespace AlgebraicGeometry.Scheme.PhComparison

/-- Direct image `π_{X,*}` on abelian sheaves along the site functor `π_X` from the small étale
site of `X` to the iterated étale slice, at the topology-comparison coefficient universe. -/
def piPushforward {S : Scheme.{u}} (X : Over S) :
    Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (piSiteFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    X.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over X)

/-- Direct image `π_{X,*}` is sheaf pushforward along `piSiteFunctor X`. -/
theorem piPushforward_eq {S : Scheme.{u}} (X : Over S) :
    piPushforward X =
      (piSiteFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        X.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over X) :=
  rfl

/-- Direct image `π_{X,*}` is additive. -/
instance piPushforward_additive {S : Scheme.{u}} (X : Over S) :
    (piPushforward X).Additive :=
  inferInstanceAs
    ((piSiteFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      X.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over X)).Additive

/-- Sheaf-level adjunction `π_X⁻¹ ⊣ π_{X,*}`. -/
def piAdjunction {S : Scheme.{u}} (X : Over S) :
    piInverseImage X ⊣ piPushforward X :=
  (piSiteFunctor X).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    X.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over X)

/-- Direct image `a_{X,*}` on abelian sheaves from the iterated ph slice `(Sch/S)_ph / X` to the
small étale site of `X`. -/
def aPushforward {S : Scheme.{u}} (X : Over S) :
    Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  comparisonTopologyPushforwardAb (etale_le_ph S) X ⋙ piPushforward X

/-- Direct image `a_{X,*}` is the composite `ε_{X,*} ⋙ π_{X,*}`. -/
theorem aPushforward_eq {S : Scheme.{u}} (X : Over S) :
    aPushforward X = comparisonTopologyPushforwardAb (etale_le_ph S) X ⋙ piPushforward X :=
  rfl

/-- Direct image `a_{X,*}` is additive. -/
instance aPushforward_additive {S : Scheme.{u}} (X : Over S) : (aPushforward X).Additive :=
  inferInstanceAs
    ((comparisonTopologyPushforwardAb (etale_le_ph S) X ⋙ piPushforward X).Additive)

/-- Sheaf-level adjunction `a_X⁻¹ ⊣ a_{X,*}`. -/
def aAdjunction {S : Scheme.{u}} (X : Over S) : aInverseImage X ⊣ aPushforward X :=
  (piAdjunction X).comp
    (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} (etale_le_ph S) X)

/-- Sheaf-level `a_X⁻¹ ⊣ a_{X,*}` is the composite of `π_X⁻¹ ⊣ π_{X,*}` with
`ε_X⁻¹ ⊣ ε_{X,*}`. -/
theorem aAdjunction_eq {S : Scheme.{u}} (X : Over S) :
    aAdjunction X =
      (piAdjunction X).comp
        (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} (etale_le_ph S) X) :=
  rfl

/-- The bounded-below right-derived functor of `a_{X,*}` exists. -/
instance aPushforward_hasRightDerivedFunctor {S : Scheme.{u}} (X : Over S) :
    (aPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1})) :=
  sorry

/-- Bounded-below derived direct image `Ra_{X,*}` on `D⁺`. -/
def plusAPushforward {S : Scheme.{u}} (X : Over S) :
    DerivedCategory.Plus
      (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.right (aPushforward X)

/-- Derived direct image `Ra_{X,*}` is the bounded-below right-derived functor of abelian
`a_{X,*}`. -/
theorem plusAPushforward_eq {S : Scheme.{u}} (X : Over S) :
    plusAPushforward X = Adjunction.Derived.Plus.right (aPushforward X) :=
  rfl

/-- Bounded-below derived adjunction `a_X⁻¹ ⊣ Ra_{X,*}` on `D⁺`. -/
def plusAAdjunction {S : Scheme.{u}} (X : Over S) :
    plusAInverseImage X ⊣ plusAPushforward X :=
  Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseImage X))
    (aPushforward X) (aAdjunction X)

/-- The `D⁺` adjunction `a_X⁻¹ ⊣ Ra_{X,*}` is the exact-left bounded-below derived adjunction of
abelian `a_X⁻¹ ⊣ a_{X,*}`. -/
theorem plusAAdjunction_eq {S : Scheme.{u}} (X : Over S) :
    plusAAdjunction X =
      Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseImage X))
        (aPushforward X) (aAdjunction X) :=
  rfl

/-- The sheaf-level adjunction unit of `a_X⁻¹ ⊣ a_{X,*}` is an isomorphism on locally torsion
abelian sheaves. -/
theorem aAdjunction_unit_isIso {S : Scheme.{u}} {X : Over S}
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) :
    IsIso ((aAdjunction X).unit.app F) := sorry

/-- Higher direct images `R^q a_{X,*} (a_X⁻¹ F)` vanish for `0 < q` on locally torsion abelian
sheaves. -/
theorem aPushforward_rightDerived_aInverseImage_isZero {S : Scheme.{u}} {X : Over S}
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (q : ℕ) (hq : 0 < q) :
    IsZero
      (((aPushforward X).rightDerived q).obj ((aInverseImage X).obj F)) := sorry

/-- For a scheme `X` and a bounded-below complex of étale abelian sheaves with locally
torsion cohomology, the canonical derived adjunction unit
`K ⟶ Ra_{X,*} (a_X⁻¹ K)` is an isomorphism. -/
theorem plusAAdjunction_unit_isIso {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K) :
    IsIso ((plusAAdjunction (Over.mk (𝟙 X))).unit.app K) := sorry

end AlgebraicGeometry.Scheme.PhComparison

end

end
