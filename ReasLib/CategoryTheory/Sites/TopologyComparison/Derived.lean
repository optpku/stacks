module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Sheaf
public import ReasLib.CategoryTheory.Sites.Over.Derived
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.RightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Square
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived functors for a topology comparison

The identity-site comparison is exact on abelian sheaves, so its bounded-below derived inverse
image is owned by the exact-functor API.  Direct images are only additive in general and therefore
use the canonical bounded or unbounded total right-derived owners.  This separation keeps
resolution assumptions on the right-derived side instead of imposing them on an exact inverse
image.
-/

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.GrothendieckTopology.Derived

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

section

variable (hle : τ' ≤ τ) (X : C)
variable [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]

/-- The quasi-isomorphism denominator on the homotopy category of abelian sheaves over a
localized site. -/
@[stacks 0EZF "topology-comparison derived denominator"]
abbrev qis (J : GrothendieckTopology C) (X : C) :
    MorphismProperty
      (HomotopyCategory (Sheaf (J.over X) AddCommGrpCat.{max u v}) (up ℤ)) :=
  HomotopyCategory.quasiIso (Sheaf (J.over X) AddCommGrpCat.{max u v}) (up ℤ)

/-- The homotopy localization functor for abelian sheaves over a localized site. -/
@[stacks 0EZF "topology-comparison homotopy localization"]
noncomputable abbrev qh (J : GrothendieckTopology C) (X : C) :
    HomotopyCategory (Sheaf (J.over X) AddCommGrpCat.{max u v}) (up ℤ) ⥤
      DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max u v}) :=
  DerivedCategory.Qh

/-- The unbounded total right-derived direct image for a topology comparison. -/
@[stacks 0EZF "unbounded topology-comparison direct image"]
noncomputable abbrev pushforward
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (comparisonTopologyPushforwardAb hle X))
      (HomotopyCategory.quasiIso
        (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (up ℤ))] :
    DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) :=
  Functor.RightDerived.Homotopy.functor (comparisonTopologyPushforwardAb hle X)

/-- The unbounded exact derived inverse image for a topology comparison. -/
@[stacks 0EZF "unbounded topology-comparison inverse image"]
noncomputable abbrev pullback :
    DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) :=
  (comparisonTopologyPullbackAb hle X).mapDerivedCategory

/-- The exact inverse-image factorization through the source derived category. -/
@[stacks 0EZF "topology-comparison inverse-image factorization"]
noncomputable abbrev pullbackFactors :
    qh τ' X ⋙ pullback hle X ⟶
      Functor.Homotopy.toDerived (comparisonTopologyPullbackAb hle X) :=
  (comparisonTopologyPullbackAb hle X).mapDerivedCategoryFactorsh.hom

/-- The unit exhibiting topology-comparison direct image as a total right-derived functor. -/
@[stacks 0EZF "topology-comparison direct-image derived unit"]
noncomputable abbrev pushforwardUnit
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (comparisonTopologyPushforwardAb hle X)) (qis τ X)] :
    Functor.Homotopy.toDerived (comparisonTopologyPushforwardAb hle X) ⟶
      qh τ X ⋙ pushforward hle X :=
  Functor.RightDerived.Homotopy.unit (comparisonTopologyPushforwardAb hle X)

/-- Exact topology-comparison inverse image is a left-derived model on homotopy categories. -/
@[stacks 0EZF "topology-comparison inverse image is left derived", instance]
noncomputable instance pullback_isLeftDerived :
    (pullback hle X).IsLeftDerivedFunctor (pullbackFactors hle X) (qis τ' X) := sorry

/-- Topology-comparison direct image is its canonical total right-derived model. -/
@[stacks 0EZF "topology-comparison direct image is right derived", instance]
noncomputable instance pushforward_isRightDerived
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (comparisonTopologyPushforwardAb hle X)) (qis τ X)] :
    (pushforward hle X).IsRightDerivedFunctor (pushforwardUnit hle X) (qis τ X) := sorry

/-- The structure map for deriving `pullback hle X ⋙ pushforward hle X` from the left. -/
@[stacks 0EZF "topology-comparison pullback-pushforward derived structure"]
noncomputable abbrev pullbackPushforwardFactors
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (comparisonTopologyPushforwardAb hle X)) (qis τ X)] :
    qh τ' X ⋙ (pullback hle X ⋙ pushforward hle X) ⟶
      (comparisonTopologyPullbackAb hle X).mapHomotopyCategory (up ℤ) ⋙
        (qh τ X ⋙ pushforward hle X) :=
  (Functor.associator (qh τ' X) (pullback hle X) (pushforward hle X)).inv ≫
    Functor.whiskerRight (pullbackFactors hle X) (pushforward hle X)

/-- The structure map for deriving `pushforward hle X ⋙ pullback hle X` from the right. -/
@[stacks 0EZF "topology-comparison pushforward-pullback derived structure"]
noncomputable abbrev pushforwardPullbackUnit
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (comparisonTopologyPushforwardAb hle X)) (qis τ X)] :
    (comparisonTopologyPushforwardAb hle X).mapHomotopyCategory (up ℤ) ⋙
        (qh τ' X ⋙ pullback hle X) ⟶
      qh τ X ⋙ (pushforward hle X ⋙ pullback hle X) :=
  Functor.whiskerRight (pushforwardUnit hle X) (pullback hle X) ≫
    (Functor.associator (qh τ X) (pushforward hle X) (pullback hle X)).hom

/-- The absolute-derived compatibility needed to retain the topology-comparison adjunction after
passing to unbounded derived categories. -/
@[stacks 0EZF "topology-comparison derived adjunction pair"]
class HasPair
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (comparisonTopologyPushforwardAb hle X)) (qis τ X)] : Prop where
  /-- The pullback-pushforward composite remains a left-derived functor. -/
  pullbackPushforward :
    (pullback hle X ⋙ pushforward hle X).IsLeftDerivedFunctor
      (pullbackPushforwardFactors hle X) (qis τ' X)
  /-- The pushforward-pullback composite remains a right-derived functor. -/
  pushforwardPullback :
    (pushforward hle X ⋙ pullback hle X).IsRightDerivedFunctor
      (pushforwardPullbackUnit hle X) (qis τ X)

attribute [instance] HasPair.pullbackPushforward HasPair.pushforwardPullback

/-- The canonical topology-comparison adjunction on unbounded derived categories. -/
@[stacks 0EZF "topology-comparison derived adjunction"]
noncomputable def adjunction
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (comparisonTopologyPushforwardAb hle X)) (qis τ X)]
    [hpair : HasPair hle X] :
    pullback hle X ⊣ pushforward hle X :=
  @Adjunction.derived
    _ _ _ _ _ _ _ _ _ _
    (Adjunction.mapHomotopyCategoryAdjunction
      (comparisonTopologyAdjunction AddCommGrpCat.{max u v} hle X))
    (qh τ' X) (qh τ X) (qis τ' X) (qis τ X) inferInstance inferInstance
    (pullback hle X) (pushforward hle X) (pullbackFactors hle X) (pushforwardUnit hle X)
    (pullback_isLeftDerived hle X) (pushforward_isRightDerived hle X)
    hpair.pullbackPushforward hpair.pushforwardPullback

/-- The canonical unit `𝟭 ⟶ pullback hle X ⋙ pushforward hle X` of the derived topology
comparison. -/
@[stacks 0EZF "topology-comparison derived unit"]
noncomputable abbrev unit
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (comparisonTopologyPushforwardAb hle X)) (qis τ X)]
    [HasPair hle X] :
    𝟭 (DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v})) ⟶
      pullback hle X ⋙ pushforward hle X :=
  (adjunction hle X).unit

/-! The `Plus` namespace is the canonical bounded-below interface. -/
namespace Plus

section Pullback

variable (hle : τ' ≤ τ) (X : C)
variable [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]

/-- Lemma 21.30.8: the bounded-below derived inverse image for a topology comparison. -/
@[stacks 0EZF "bounded-below topology-comparison inverse image"]
noncomputable abbrev pullback :
    DerivedCategory.Plus (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory.Plus (Sheaf (τ.over X) AddCommGrpCat.{max u v}) :=
  Adjunction.Derived.Plus.left (comparisonTopologyPullbackAbExact hle X)

/-- The localization factor of the exact bounded-below inverse image. -/
@[stacks 0EZF "bounded-below topology-comparison inverse-image factor"]
noncomputable abbrev pullbackFactor :
    DerivedCategory.Plus.Qh ⋙ pullback hle X ⟶
      (comparisonTopologyPullbackAb hle X).toBoundedBelowDerived :=
  Adjunction.Derived.Plus.leftFactor (comparisonTopologyPullbackAbExact hle X)

end Pullback

section RightDerived

variable (hle : τ' ≤ τ) (X : C)
variable [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [Functor.HasRightDerivedFunctor
  ((comparisonTopologyPushforwardAb hle X).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ.over X) AddCommGrpCat.{max u v}))]

/-- Lemma 21.30.8: the bounded-below derived direct image for a topology comparison. -/
@[stacks 0EZF "bounded-below topology-comparison direct image"]
noncomputable abbrev pushforward :
    DerivedCategory.Plus (Sheaf (τ.over X) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory.Plus (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) :=
  Adjunction.Derived.Plus.right (comparisonTopologyPushforwardAb hle X)

/-- The canonical localization unit of the bounded-below direct image. -/
@[stacks 0EZF "bounded-below topology-comparison direct-image unit"]
noncomputable abbrev pushforwardUnit :
    (comparisonTopologyPushforwardAb hle X).toBoundedBelowDerived ⟶
      DerivedCategory.Plus.Qh ⋙ pushforward hle X :=
  Adjunction.Derived.Plus.rightUnit (comparisonTopologyPushforwardAb hle X)

/-- The localization factor for the composite `pullback ⋙ pushforward`. -/
@[stacks 0EZF "bounded-below topology-comparison composite factor"]
noncomputable abbrev pullbackPushforwardFactor :
    DerivedCategory.Plus.Qh ⋙ (pullback hle X ⋙ pushforward hle X) ⟶
      (comparisonTopologyPullbackAb hle X).mapHomotopyCategoryPlus ⋙
        (DerivedCategory.Plus.Qh ⋙ pushforward hle X) :=
  Adjunction.Derived.Plus.leftRightFactor
    (comparisonTopologyPullbackAbExact hle X)
    (comparisonTopologyPushforwardAb hle X)

/-- The localization unit for the composite `pushforward ⋙ pullback`. -/
@[stacks 0EZF "bounded-below topology-comparison composite unit"]
noncomputable abbrev pushforwardPullbackUnit :
    (comparisonTopologyPushforwardAb hle X).mapHomotopyCategoryPlus ⋙
        (DerivedCategory.Plus.Qh ⋙ pullback hle X) ⟶
      DerivedCategory.Plus.Qh ⋙ (pushforward hle X ⋙ pullback hle X) :=
  Adjunction.Derived.Plus.rightLeftUnit
    (comparisonTopologyPullbackAbExact hle X)
    (comparisonTopologyPushforwardAb hle X)

/-- The bounded-below topology-comparison adjunction. -/
@[stacks 0EZF "bounded-below topology-comparison derived adjunction"]
noncomputable def adjunction :
    pullback hle X ⊣ pushforward hle X :=
  Adjunction.Derived.Plus.adjunction
    (comparisonTopologyPullbackAbExact hle X)
    (comparisonTopologyPushforwardAb hle X)
    (comparisonTopologyAdjunction AddCommGrpCat.{max u v} hle X)

/-- The unit of the bounded-below topology-comparison adjunction. -/
@[stacks 0EZF "bounded-below topology-comparison derived unit"]
noncomputable abbrev unit :
    𝟭 (DerivedCategory.Plus (Sheaf (τ'.over X) AddCommGrpCat.{max u v})) ⟶
      pullback hle X ⋙ pushforward hle X :=
  (adjunction hle X).unit

end RightDerived

section Relocalization

variable (hle : τ' ≤ τ) {X Y : C} (f : X ⟶ Y)
variable [HasPullbacksAlong f]
variable [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [HasSheafify (τ.over Y) AddCommGrpCat.{max u v}]
variable [HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [HasSheafify (τ'.over Y) AddCommGrpCat.{max u v}]

/-- The canonical bounded-below exact-derived square for relocalization and a topology
comparison. -/
@[stacks 0EZF "bounded-below topology-comparison relocalization square"]
noncomputable def overMapPullbackComparisonIso :
    Derived.Over.Plus.pullback τ' f ⋙ pullback hle X ≅
      pullback hle Y ⋙ Derived.Over.Plus.pullback τ f :=
  ExactFunctor.Derived.Plus.squareIso
    (τ'.overMapPullbackExact f)
    (comparisonTopologyPullbackAbExact hle X)
    (comparisonTopologyPullbackAbExact hle Y)
    (τ.overMapPullbackExact f)
    (GrothendieckTopology.overMapPullbackComparisonExactIso hle f)

section BaseChange

variable [∀ P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
  (Over.map f).op.HasPointwiseRightKanExtension P]
variable [Functor.HasRightDerivedFunctor
  (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
    (τ'.over X) (τ'.over Y)).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))]
variable [Functor.HasRightDerivedFunctor
  (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
    (τ.over X) (τ.over Y)).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ.over X) AddCommGrpCat.{max u v}))]

/-- The bounded-below derived base-change transformation
`R f_{τ',*} ⋙ ε_Y⁻¹ ⟶ ε_X⁻¹ ⋙ R f_{τ,*}`. -/
@[stacks 0EZF "bounded-below topology-comparison base change"]
noncomputable def baseChange :
    Derived.Over.Plus.pushforward τ' f ⋙ pullback hle Y ⟶
      pullback hle X ⋙ Derived.Over.Plus.pushforward τ f :=
  DerivedBaseChange.map
    (Derived.Over.Plus.adjunction τ' f)
    (Derived.Over.Plus.adjunction τ f)
    (overMapPullbackComparisonIso hle f).symm

/-- The component of bounded-below topology-comparison base change at `K`. -/
@[stacks 0EZF "bounded-below topology-comparison base-change component"]
noncomputable abbrev baseChangeApp
    (K : DerivedCategory.Plus
      (Sheaf (τ'.over X) AddCommGrpCat.{max u v})) :
    (pullback hle Y).obj ((Derived.Over.Plus.pushforward τ' f).obj K) ⟶
      (Derived.Over.Plus.pushforward τ f).obj ((pullback hle X).obj K) :=
  (baseChange hle f).app K

section PushforwardComparison

variable [Functor.HasRightDerivedFunctor
  ((comparisonTopologyPushforwardAb hle X).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ.over X) AddCommGrpCat.{max u v}))]
variable [Functor.HasRightDerivedFunctor
  ((comparisonTopologyPushforwardAb hle Y).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ.over Y) AddCommGrpCat.{max u v}))]

/-- The right mate of `baseChange` along the two topology-comparison adjunctions.  This is the
canonical bounded-below direct-image comparison
`R ε_{X,*} ⋙ R f_{τ',*} ⟶ R f_{τ,*} ⋙ R ε_{Y,*}`; local-vanishing hypotheses belong only to
statements asserting that its degreewise projections are invertible. -/
@[stacks 0EZA "bounded-below topology-comparison direct-image comparison"]
noncomputable def pushforwardComparison :
    pushforward hle X ⋙ Derived.Over.Plus.pushforward τ' f ⟶
      Derived.Over.Plus.pushforward τ f ⋙ pushforward hle Y :=
  (CategoryTheory.mateEquiv (adjunction hle X) (adjunction hle Y)
    (baseChange hle f)).natTrans

/-- The mate construction is reversible; this specification keeps the left-square comparison
available to downstream code without unfolding the chosen adjunctions. -/
@[stacks 0EZA "bounded-below direct-image comparison mate specification"]
theorem pushforwardComparison_mate :
    (CategoryTheory.mateEquiv
      (G := Derived.Over.Plus.pushforward τ' f)
      (H := Derived.Over.Plus.pushforward τ f)
      (adjunction hle X) (adjunction hle Y)).symm
        (TwoSquare.mk
          (pushforward hle X)
          (Derived.Over.Plus.pushforward τ f)
          (Derived.Over.Plus.pushforward τ' f)
          (pushforward hle Y)
          (pushforwardComparison hle f)) =
      TwoSquare.mk
        (Derived.Over.Plus.pushforward τ' f)
        (pullback hle X)
        (pullback hle Y)
        (Derived.Over.Plus.pushforward τ f)
        (baseChange hle f) := sorry

/-- The component of `pushforwardComparison` at a bounded-below complex. -/
@[stacks 0EZA "bounded-below direct-image comparison component"]
noncomputable abbrev pushforwardComparisonApp
    (K : DerivedCategory.Plus
      (Sheaf (τ.over X) AddCommGrpCat.{max u v})) :
    (Derived.Over.Plus.pushforward τ' f).obj ((pushforward hle X).obj K) ⟶
      (pushforward hle Y).obj ((Derived.Over.Plus.pushforward τ f).obj K) :=
  (pushforwardComparison hle f).app K

/-- The degreewise homology arrow obtained from the canonical bounded-below direct-image
comparison at a sheaf placed in degree zero.  This is a derived-category homology view; it is
deliberately kept separate from the ordinary `rightDerived` degree presentation, whose
comparison requires an additional named degree-isomorphism bridge. -/
@[stacks 0EZA "homology component of the bounded-below direct-image comparison"]
noncomputable abbrev pushforwardComparisonHomologyApp
    (i : ℤ) (F : Sheaf (τ.over X) AddCommGrpCat.{max u v}) :
    (DerivedCategory.Plus.homologyFunctor
        (Sheaf (τ'.over Y) AddCommGrpCat.{max u v}) i).obj
        ((Derived.Over.Plus.pushforward τ' f).obj
          ((pushforward hle X).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (0 : ℤ)).obj F))) ⟶
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf (τ'.over Y) AddCommGrpCat.{max u v}) i).obj
        ((pushforward hle Y).obj
          ((Derived.Over.Plus.pushforward τ f).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (0 : ℤ)).obj F))) :=
  (DerivedCategory.Plus.homologyFunctor
      (Sheaf (τ'.over Y) AddCommGrpCat.{max u v}) i).map
    (pushforwardComparisonApp hle f
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (0 : ℤ)).obj F))

end PushforwardComparison

end BaseChange

end Relocalization

section ExplicitPullbacks

variable (hle : τ' ≤ τ) {X Y : C} (f : X ⟶ Y)
variable (hp : HasPullbacksAlong f)
variable [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [HasSheafify (τ.over Y) AddCommGrpCat.{max u v}]
variable [HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [HasSheafify (τ'.over Y) AddCommGrpCat.{max u v}]
variable [∀ P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
  (Over.map f).op.HasPointwiseRightKanExtension P]
variable [Functor.HasRightDerivedFunctor
  (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
    (τ'.over X) (τ'.over Y)).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))]
variable [Functor.HasRightDerivedFunctor
  (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
    (τ.over X) (τ.over Y)).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ.over X) AddCommGrpCat.{max u v}))]

/-- The bounded-below base-change transformation with pullback existence supplied by an explicit
source bridge.  Invertibility is deliberately left as a separate, hypothesis-sensitive theorem. -/
@[stacks 0EZF "bounded-below topology-comparison base-change bridge"]
noncomputable def baseChangeOf :
    Derived.Over.Plus.pushforward τ' f ⋙ pullback hle Y ⟶
      pullback hle X ⋙ Derived.Over.Plus.pushforward τ f :=
  letI : HasPullbacksAlong f := hp
  baseChange hle f

section PushforwardComparison

variable [Functor.HasRightDerivedFunctor
  ((comparisonTopologyPushforwardAb hle X).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ.over X) AddCommGrpCat.{max u v}))]
variable [Functor.HasRightDerivedFunctor
  ((comparisonTopologyPushforwardAb hle Y).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ.over Y) AddCommGrpCat.{max u v}))]

/-- The direct-image comparison with pullback existence supplied by an explicit geometric
certificate.  This is the source-facing bridge for a morphism-property witness. -/
@[stacks 0EZA "explicit bounded-below direct-image comparison bridge"]
noncomputable def pushforwardComparisonOf :
    pushforward hle X ⋙ Derived.Over.Plus.pushforward τ' f ⟶
      Derived.Over.Plus.pushforward τ f ⋙ pushforward hle Y :=
  letI : HasPullbacksAlong f := hp
  pushforwardComparison hle f

/-- The homology component of `pushforwardComparisonOf` at a sheaf in degree zero.  This is the
canonical degreewise comparison when pullbacks along `f` are supplied by an explicit geometric
certificate rather than an ambient instance. -/
@[stacks 0EZA "explicit homology component of the direct-image comparison"]
noncomputable def pushforwardComparisonHomologyAppOf
    (i : ℤ) (F : Sheaf (τ.over X) AddCommGrpCat.{max u v}) :
    (DerivedCategory.Plus.homologyFunctor
        (Sheaf (τ'.over Y) AddCommGrpCat.{max u v}) i).obj
        ((Derived.Over.Plus.pushforward τ' f).obj
          ((pushforward hle X).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (0 : ℤ)).obj F))) ⟶
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf (τ'.over Y) AddCommGrpCat.{max u v}) i).obj
        ((pushforward hle Y).obj
          ((Derived.Over.Plus.pushforward τ f).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (0 : ℤ)).obj F))) :=
  (DerivedCategory.Plus.homologyFunctor
      (Sheaf (τ'.over Y) AddCommGrpCat.{max u v}) i).map
    ((pushforwardComparisonOf hle f hp).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (0 : ℤ)).obj F))

end PushforwardComparison

end ExplicitPullbacks

end Plus

end

end CategoryTheory.GrothendieckTopology.Derived
