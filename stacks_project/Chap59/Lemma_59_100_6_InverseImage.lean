/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Derived
public import stacks_project.Chap59.Lemma_59_100_5_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fppf/étale inverse images

This leaf owns the scheme-level comparison `étale ≤ fppf`, the identity-site functors
`ε_{X,*}` and `ε_X⁻¹`, the composite inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹`, and the
small-étale / big-fppf direct images used by Lemma 59.100.6.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FppfEtale

/-- Every étale covering of schemes is an fppf covering. -/
theorem etale_le_fppf : etaleTopology.{u} ≤ fppfTopology.{u} := sorry

/-- Abelian-group-valued sheafification exists on the small étale site at the
topology-comparison coefficient universe. -/
instance smallEtale_hasSheafify_addCommGrp (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} := sorry

/-- Abelian-group-valued sheafification exists on every big étale slice at the
topology-comparison coefficient universe. -/
instance etaleOver_hasSheafify_addCommGrp (X : Scheme.{u}) :
    HasSheafify (etaleTopology.over X) AddCommGrpCat.{u + 1} := sorry

/-- Abelian-group-valued sheafification exists on every big fppf slice at the
topology-comparison coefficient universe. -/
instance fppfOver_hasSheafify_addCommGrp (X : Scheme.{u}) :
    HasSheafify (fppfTopology.over X) AddCommGrpCat.{u + 1} := sorry

/-- Identity-base étale relocalization admits left Kan extensions on abelian presheaves. -/
instance relocalizationFunctor_id_op_hasLeftKanExtension
    (X : Scheme.{u}) (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P := sorry

/-- Postcomposition on scheme slices admits pointwise right Kan extensions on abelian
presheaves at the topology-comparison coefficient universe. -/
instance overMap_op_hasPointwiseRightKanExtension_addCommGrp
    {X Y : Scheme.{u}} (f : X ⟶ Y) (P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (Over.map f).op.HasPointwiseRightKanExtension P := sorry

/-- Direct image `ε_{X,*}` on abelian sheaves from the big fppf slice to the big étale slice. -/
abbrev epsilonPushforward (X : Scheme.{u}) :
    Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} :=
  comparisonTopologyPushforwardAb etale_le_fppf X

/-- Inverse image `ε_X⁻¹` on abelian sheaves from the big étale slice to the big fppf slice. -/
abbrev epsilonPullback (X : Scheme.{u}) :
    Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1} :=
  comparisonTopologyPullbackAb etale_le_fppf X

/-- Inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on abelian sheaves from the small étale site of `X`
to the big fppf slice. -/
abbrev aInverseAb (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1} :=
  piInverseImage X ⋙ epsilonPullback X

/-- Inverse image `a_X⁻¹` is the composite `π_X⁻¹ ⋙ ε_X⁻¹`. -/
theorem aInverseAb_eq (X : Scheme.{u}) :
    aInverseAb X = piInverseImage X ⋙ epsilonPullback X := sorry

/-- The canonical comparison map `π_X⁻¹ F ⟶ ε_{X,*}(a_X⁻¹ F)`. -/
def aInverse_unit (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (piInverseImage X).obj F ⟶
      (epsilonPushforward X).obj ((aInverseAb X).obj F) :=
  (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_fppf X).unit.app
    ((piInverseImage X).obj F)

/-- `aInverse_unit` is the topology-comparison adjunction unit at `π_X⁻¹ F`. -/
theorem aInverse_unit_eq (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    aInverse_unit X F =
      (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_fppf X).unit.app
        ((piInverseImage X).obj F) := sorry

/-- Inverse image `π_X⁻¹` is additive at the topology-comparison coefficient universe. -/
instance piInverseImage_additive (X : Scheme.{u}) :
    (piInverseImage X).Additive := sorry

/-- Inverse image `π_X⁻¹` preserves finite limits. -/
instance piInverseImage_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (piInverseImage X) := sorry

/-- Inverse image `π_X⁻¹` preserves finite colimits. -/
instance piInverseImage_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (piInverseImage X) := sorry

/-- Direct image of abelian small-étale sheaves along a morphism of schemes. -/
abbrev smallPushforwardAb {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- `smallPushforwardAb` is sheaf pushforward along `smallEtalePullback`. -/
theorem smallPushforwardAb_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallPushforwardAb f =
      (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology := sorry

/-- Direct image of abelian sheaves along a morphism of schemes on the big fppf slices. -/
abbrev fppfPushforwardAb {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (fppfTopology.over Y) AddCommGrpCat.{u + 1} :=
  (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (fppfTopology.over X) (fppfTopology.over Y)

/-- `fppfPushforwardAb` is the cocontinuous sheaf pushforward along `Over.map`. -/
theorem fppfPushforwardAb_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    fppfPushforwardAb f =
      (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (fppfTopology.over X) (fppfTopology.over Y) := sorry

/-- Direct image of abelian small-étale sheaves is additive. -/
instance smallPushforwardAb_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallPushforwardAb f).Additive := sorry

/-- Abelian sheaves on small étale sites have injective resolutions at the
topology-comparison coefficient universe. -/
instance smallEtale_hasInjectiveResolutions_addCommGrp (X : Scheme.{u}) :
    HasInjectiveResolutions
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := sorry

/-- Abelian sheaves on big fppf slices have injective resolutions at the
topology-comparison coefficient universe. -/
instance fppfOver_hasInjectiveResolutions (X : Scheme.{u}) :
    HasInjectiveResolutions
      (Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1}) := sorry

/-- The bounded-below right-derived functor of `ε_{X,*}` exists. -/
instance epsilonPushforward_hasRightDerivedFunctor (X : Scheme.{u}) :
    (epsilonPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1})) := sorry

/-- The bounded-below right-derived functor of small étale direct image exists. -/
instance smallPushforwardAb_hasRightDerivedFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallPushforwardAb f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) := sorry

/-- The bounded-below right-derived functor of big fppf direct image exists. -/
instance fppfPushforwardAb_hasRightDerivedFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (fppfPushforwardAb f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1})) := sorry

/-- Exact inverse image `π_X⁻¹` on abelian small-étale sheaves. -/
abbrev piExact (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (piInverseImage X)

/-- Bounded-below derived inverse image `π_X⁻¹` on `D⁺`. -/
abbrev piInverseImagePlus (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) :=
  ExactFunctor.Derived.Plus.functor (piExact X)

/-- Bounded-below derived inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on `D⁺`. -/
abbrev aInverseAbPlus (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1}) :=
  piInverseImagePlus X ⋙ Derived.Plus.pullback etale_le_fppf X

/-- Derived inverse image `a_X⁻¹` is the composite of derived `π_X⁻¹` with topology-comparison
inverse image. -/
theorem aInverseAbPlus_eq (X : Scheme.{u}) :
    aInverseAbPlus X = piInverseImagePlus X ⋙ Derived.Plus.pullback etale_le_fppf X :=
  sorry

end AlgebraicGeometry.Scheme.FppfEtale

end
