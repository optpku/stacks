/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Derived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Exact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.Adjunction

/-!
# Fppf/étale inverse images of algebraic spaces

The refinement `étale ≤ fppf` induces inverse image `ε_X⁻¹` from the big étale
slice to the big fppf slice. Its composite with small-to-big étale inverse image
is `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹`, on abelian sheaves and on bounded-below derived categories.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FppfEtale

variable {S : Scheme.{u}}

/-- Every étale covering of algebraic spaces over `S` is an fppf covering. -/
theorem etale_le_fppf :
    (etaleTopology : GrothendieckTopology (AlgebraicSpace S)) ≤ fppfTopology S := sorry




/-- Identity-base étale relocalization admits left Kan extensions on abelian presheaves. -/
instance relocalizationFunctor_id_op_hasLeftKanExtension
    (X : AlgebraicSpace S) (P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P := sorry

/-- Identity-base étale relocalization left Kan extensions preserve finite limits. -/
instance relocalizationFunctor_id_op_lan_preservesFiniteLimits (X : AlgebraicSpace S) :
    PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 X)).op.lan :
        ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
          ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})) := sorry

/-- Postcomposition on algebraic-space slices admits pointwise right Kan extensions on abelian
presheaves at the topology-comparison coefficient universe. -/
instance overMap_op_hasPointwiseRightKanExtension_addCommGrp
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (Over.map f).op.HasPointwiseRightKanExtension P := sorry

/-- Inverse image `ε_X⁻¹` on abelian sheaves from the big étale slice to the big fppf slice. -/
abbrev epsilonPullback (X : AlgebraicSpace S) :
    Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1} :=
  comparisonTopologyPullbackAb etale_le_fppf X

/-- Inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on abelian sheaves from the small étale site of `X`
to the big fppf slice. -/
abbrev aInverseAb (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1} :=
  etalePiInverseImage X ⋙ epsilonPullback X

/-- Inverse image `a_X⁻¹` is the composite `π_X⁻¹ ⋙ ε_X⁻¹`. -/
theorem aInverseAb_eq (X : AlgebraicSpace S) :
    aInverseAb X = etalePiInverseImage X ⋙ epsilonPullback X := rfl

/-- Exact inverse image `π_X⁻¹` on abelian small-étale sheaves. -/
abbrev etalePiExact (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (etalePiInverseImage X)

/-- Bounded-below derived inverse image `π_X⁻¹` on `D⁺`. -/
abbrev piInverseImagePlus (X : AlgebraicSpace S) :
    DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  ExactFunctor.Derived.Plus.functor (etalePiExact X)

/-- Bounded-below derived inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on `D⁺`. -/
abbrev aInverseAbPlus (X : AlgebraicSpace S) :
    DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1}) :=
  piInverseImagePlus X ⋙ Derived.Plus.pullback etale_le_fppf X

/-- Derived inverse image `a_X⁻¹` is the composite of derived `π_X⁻¹` with topology-comparison
inverse image. -/
theorem aInverseAbPlus_eq (X : AlgebraicSpace S) :
    aInverseAbPlus X =
      piInverseImagePlus X ⋙ Derived.Plus.pullback etale_le_fppf X := rfl

/-- Exact inverse image `f_small⁻¹` on abelian small-étale sheaves. -/
abbrev smallInverseExact {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (sheafInverseImage AddCommGrpCat.{u + 1} f)

/-- Bounded-below derived inverse image `f_small⁻¹` on `D⁺`. -/
abbrev smallInverseImagePlus {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.left (smallInverseExact f)

/-- `smallInverseImagePlus` is the bounded-below derived action of `sheafInverseImage`. -/
theorem smallInverseImagePlus_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    smallInverseImagePlus f = Adjunction.Derived.Plus.left (smallInverseExact f) := rfl

/-- Sheaf-level adjunction `f_small⁻¹ ⊣ f_small,*`. -/
def sheafPushforwardAdjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    sheafInverseImage AddCommGrpCat.{u + 1} f ⊣ sheafPushforward AddCommGrpCat.{u + 1} f :=
  Adjunction.comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f)
      AddCommGrpCat.{u + 1} (smallEtaleTopology Y) (spacesEtaleTopology X))
    ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X))

/-- `sheafPushforwardAdjunction` is the composite of the étale-base-change and small-étale-inclusion
adjunctions. -/
theorem sheafPushforwardAdjunction_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    sheafPushforwardAdjunction f =
      Adjunction.comp
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f)
          AddCommGrpCat.{u + 1} (smallEtaleTopology Y) (spacesEtaleTopology X))
        ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology X) (spacesEtaleTopology X)) := rfl

/-- Abelian sheaves on small étale sites have injective resolutions at the
topology-comparison coefficient universe. -/
instance smallEtale_hasInjectiveResolutions_addCommGrp (X : AlgebraicSpace S) :
    HasInjectiveResolutions
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) := sorry

/-- Abelian sheaves on big fppf slices have injective resolutions at the
topology-comparison coefficient universe. -/
instance fppfOver_hasInjectiveResolutions (X : AlgebraicSpace S) :
    HasInjectiveResolutions
      (Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1}) := sorry

/-- Abelian sheaves on big étale slices have injective resolutions at the
topology-comparison coefficient universe. -/
instance etaleOver_hasInjectiveResolutions (X : AlgebraicSpace S) :
    HasInjectiveResolutions
      (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1}) := sorry

/-- The bounded-below right-derived functor of small étale direct image exists. -/
instance smallPushforward_hasRightDerivedFunctor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sheafPushforward AddCommGrpCat.{u + 1} f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) := sorry

/-- The bounded-below right-derived functor of big fppf direct image exists. -/
instance fppfPushforward_hasRightDerivedFunctor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((fppfTopology S).over X) ((fppfTopology S).over Y)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1})) := sorry

/-- The bounded-below right-derived functor of big étale direct image exists. -/
instance etaleOverPushforward_hasRightDerivedFunctor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (overEtaleTopology X) (overEtaleTopology Y)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})) := sorry

end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
