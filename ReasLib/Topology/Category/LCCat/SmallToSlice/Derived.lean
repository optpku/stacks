/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.LCCat.SmallToSlice.Comparison
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Consequences
public import ReasLib.CategoryTheory.Sites.TopologyComparison.HigherDirectImage
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Homology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived comparison for the small-to-slice morphism

This leaf owns the concrete bounded-below comparison statements for the canonical small open,
Zariski, and qc sites of an object of `LCCat`.  The chapter entries are recall facades; downstream
proofs should import these declarations directly.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open TopologicalSpace
open scoped CategoryTheory CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace LCCat.SmallToSlice

section Comparison

variable (X : LCCat.{u})
variable [HasWeakSheafify (LCCat.zarTopology.over X) AddCommGrpCat.{u + 1}]
variable [HasWeakSheafify (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}]

/-- The canonical comparison map `π_X⁻¹ F ⟶ ε_{X,*}(a_X⁻¹ F)`. -/
@[stacks 0DCY "canonical comparison map for a_X⁻¹"]
noncomputable abbrev qcPushforward_aInverse_unit
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) :
    (abPullback X).obj F ⟶
      (comparisonTopologyPushforwardAb LCCat.zar_le_qc X).obj
        ((aInverseAb X).obj F) :=
  (comparisonTopologyAdjunction AddCommGrpCat.{u + 1}
    LCCat.zar_le_qc X).unit.app ((abPullback X).obj F)

/-- The source-facing invertibility assertion for `qcPushforward_aInverse_unit`. -/
@[stacks 0DCY "comparison map for a_X⁻¹ is invertible"]
theorem qcPushforward_aInverse_unit_isIso
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) :
    IsIso (qcPushforward_aInverse_unit X F) := by
  exact comparisonTopology_unit_isIso_of_isSheaf AddCommGrpCat.{u + 1}
    LCCat.zar_le_qc X ((abPullback X).obj F)
    (essImageAb_isSheafQc X ((abPullback X).obj_mem_essImage F))

variable [HasInjectiveResolutions
  (Sheaf (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1})]

/-- Positive direct images of `a_X⁻¹ F` vanish. -/
@[stacks 0DCY "higher direct-image vanishing for a_X⁻¹"]
theorem qcPushforward_aInverse_higherDirectImage_isZero
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})
    (i : ℕ) (hi : 0 < i) :
    IsZero
      (((comparisonTopologyPushforwardAb LCCat.zar_le_qc X).rightDerived i).obj
        ((aInverseAb X).obj F)) := by
  -- The comparison API uses families of instances on all slices. These are the canonical
  -- instances; enough injectives gives Ext in the coefficient universe, without a size increase.
  letI : ∀ Z : LCCat,
      HasSheafify (LCCat.qcTopology.over Z) AddCommGrpCat.{u + 1} :=
    fun Z => by infer_instance
  letI : ∀ Z : LCCat,
      HasSheafify (LCCat.zarTopology.over Z) AddCommGrpCat.{u + 1} :=
    fun Z => by infer_instance
  letI : ∀ Z : LCCat,
      HasExt.{u + 1} (Sheaf (LCCat.qcTopology.over Z) AddCommGrpCat.{u + 1}) :=
    fun Z => hasExt_of_enoughInjectives.{u + 1, u + 1, u + 2} _
  letI : ∀ Z : LCCat,
      HasInjectiveResolutions
        (Sheaf (LCCat.qcTopology.over Z) AddCommGrpCat.{u + 1}) :=
    fun Z => by infer_instance
  letI : ∀ Z : LCCat,
      HasInjectiveResolutions
        (Sheaf (LCCat.zarTopology.over Z) AddCommGrpCat.{u + 1}) :=
    fun Z => by infer_instance
  haveI : IsIso (qcPushforward_aInverse_unit X F) :=
    qcPushforward_aInverse_unit_isIso X F
  apply TopologyComparison.HigherDirectImage.comparisonPushforward_isZero LCCat.zar_le_qc
    (comparisonSituation.{u, u, u, u}) i
    (TopologyComparison.Vanishing.localVanishing_all (comparisonSituation.{u, u, u, u}) i) X
    ((aInverseAb X).obj F)
  · exact ⟨F, ⟨asIso (qcPushforward_aInverse_unit X F)⟩⟩
  · exact hi
  · exact le_rfl

/-- Lemma 21.31.10 (1): the canonical degree-zero comparison unit is invertible and all positive
higher direct images of the inverse-image coefficient vanish. -/
@[stacks 0DCY "(1)"]
theorem qcPullback_pushforward
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) :
    IsIso
        ((comparisonTopologyAdjunction AddCommGrpCat.{u + 1}
          LCCat.zar_le_qc X).unit.app ((abPullback X).obj F)) ∧
        ∀ i : ℕ, 0 < i →
        IsZero
          (((comparisonTopologyPushforwardAb LCCat.zar_le_qc X).rightDerived i).obj
            ((aInverseAb X).obj F)) := by
  exact ⟨qcPushforward_aInverse_unit_isIso X F,
    qcPushforward_aInverse_higherDirectImage_isZero X F⟩

end Comparison

section ProperHigherDirectImage

variable {X Y : LCCat.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify (LCCat.zarTopology.over X) AddCommGrpCat.{u + 1}]
variable [HasWeakSheafify (LCCat.zarTopology.over Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify
  (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [HasSheafify
  (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.qcTopology.over Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions
  (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
  (Sheaf (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1})]
variable [∀ P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
  (Over.map f).op.HasPointwiseRightKanExtension P]

/-- Lemma 21.31.10 (2): proper direct image on the small site agrees degreewise with qc direct
image after canonical inverse image. -/
@[stacks 0DCY "(2)"]
theorem proper_higherDirectImage_qc
    (hf : LCCat.proper f)
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})
    (i : ℕ) :
    IsIsomorphic
      ((aInverseAb Y).obj
        (((((Opens.map f.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (Opens.grothendieckTopology Y.obj)
          (Opens.grothendieckTopology X.obj)).rightDerived i).obj F)))
      (((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (LCCat.qcTopology.over X) (LCCat.qcTopology.over Y)).rightDerived i).obj
        ((aInverseAb X).obj F))) := sorry

end ProperHigherDirectImage

section DerivedComparison

variable (X : LCCat.{u})
variable [HasSheafify
  (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.zarTopology.over X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}]

/- The bounded-below view of `a_X⁻¹` uses the exact lift of the same underived composite. -/

/-- The canonical bounded-below derived inverse image `a_X⁻¹`. -/
@[stacks 0DCY "bounded-below canonical inverse image a_X⁻¹"]
noncomputable abbrev aInverseAbPlus :
    DerivedCategory.Plus
        (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}) :=
  abPullbackPlus X ⋙ GrothendieckTopology.Derived.Plus.pullback LCCat.zar_le_qc X

variable [Functor.HasRightDerivedFunctor
  ((comparisonTopologyPushforwardAb LCCat.zar_le_qc X).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}))]

/-- Lemma 21.31.10 (3): the canonical map
`pi_X⁻¹ K ⟶ R epsilon_{X,*}(a_X⁻¹ K)` is invertible for every `K ∈ D⁺(X)`. -/
@[stacks 0DCY "(3)"]
theorem comparisonDerivedUnit_isIso
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})) :
    IsIso
      ((GrothendieckTopology.Derived.Plus.unit LCCat.zar_le_qc X).app
        ((abPullbackPlus X).obj K)) := by
  -- As above, pin the canonical slice instances and the coefficient-sized Ext groups.
  letI : ∀ Z : LCCat,
      HasSheafify (LCCat.qcTopology.over Z) AddCommGrpCat.{u + 1} :=
    fun Z => by infer_instance
  letI : ∀ Z : LCCat,
      HasSheafify (LCCat.zarTopology.over Z) AddCommGrpCat.{u + 1} :=
    fun Z => by infer_instance
  letI : ∀ Z : LCCat,
      HasExt.{u + 1} (Sheaf (LCCat.qcTopology.over Z) AddCommGrpCat.{u + 1}) :=
    fun Z => hasExt_of_enoughInjectives.{u + 1, u + 1, u + 2} _
  letI : ∀ Z : LCCat,
      HasInjectiveResolutions
        (Sheaf (LCCat.zarTopology.over Z) AddCommGrpCat.{u + 1}) :=
    fun Z => by infer_instance
  letI : ∀ Z : LCCat, Functor.HasRightDerivedFunctor
      ((comparisonTopologyPushforwardAb LCCat.zar_le_qc Z).toBoundedBelowDerived)
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (LCCat.qcTopology.over Z) AddCommGrpCat.{u + 1})) :=
    fun Z => by infer_instance
  apply TopologyComparison.Consequences.unit_isIso_of_cohomologyIn LCCat.zar_le_qc
    (comparisonSituation.{u, u, u, u})
    (TopologyComparison.Vanishing.all (comparisonSituation.{u, u, u, u})) X
    ⟨(abPullbackPlus X).obj K, ?_⟩
  intro n
  exact ⟨(DerivedCategory.Plus.homologyFunctor _ n).obj K,
    ⟨(ExactFunctor.Derived.Plus.homologyIso (ExactFunctor.of (abPullback X)) K n).symm⟩⟩

end DerivedComparison

section ProperDerivedImage

variable {X Y : LCCat.{u}} (f : X ⟶ Y)
variable [HasSheafify
  (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [HasSheafify
  (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.zarTopology.over X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.zarTopology.over Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.qcTopology.over Y) AddCommGrpCat.{u + 1}]
variable [∀ P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
  (Over.map f).op.HasPointwiseRightKanExtension P]
variable [Functor.HasRightDerivedFunctor
  (((Opens.map f.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology Y.obj)
    (Opens.grothendieckTopology X.obj)).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}))]
variable [Functor.HasRightDerivedFunctor
  (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (LCCat.qcTopology.over X) (LCCat.qcTopology.over Y)).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}))]

/-- Lemma 21.31.10 (4): proper bounded-below direct image on the small site agrees with qc direct
image after canonical inverse image. -/
@[stacks 0DCY "(4)"]
theorem proper_derivedPushforward_qc
    (hf : LCCat.proper f)
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((aInverseAbPlus Y).obj
          ((Adjunction.Derived.Plus.right
            ((Opens.map f.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (Opens.grothendieckTopology Y.obj)
              (Opens.grothendieckTopology X.obj))).obj K))
      ((GrothendieckTopology.Derived.Over.Plus.pushforward LCCat.qcTopology f).obj
        ((aInverseAbPlus X).obj K)) := sorry

end ProperDerivedImage

section CompositeUnit

variable (X : LCCat.{u})
variable [HasSheafify
  (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.zarTopology.over X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}]
variable [Functor.HasRightDerivedFunctor
  ((comparisonTopologyPushforwardAb LCCat.zar_le_qc X).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}))]

/-- Lemma 21.31.11: the canonical bounded-below unit from the small site to its qc-site
inverse image followed by derived direct image is invertible. -/
@[stacks 0D91]
theorem qcDerivedUnit_isIso
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})) :
    IsIso
      ((((Adjunction.Derived.Plus.adjunction
          (ExactFunctor.of (abPullback X)) (abPushforward X) (abAdjunction X)).comp
        (GrothendieckTopology.Derived.Plus.adjunction LCCat.zar_le_qc X)).unit).app K) := by
  haveI : IsIso (derivedAdjunction X).unit := derivedUnit_isIso X
  let ff := (derivedAdjunction X).fullyFaithfulLOfIsIsoUnit
  letI : (ExactFunctor.of (abPullback X)).mapDerivedCategory.Full := ff.full
  letI : (ExactFunctor.of (abPullback X)).mapDerivedCategory.Faithful := ff.faithful
  -- Restrict full faithfulness along the fully faithful bounded-below inclusions.
  letI : (Adjunction.Derived.Plus.left (ExactFunctor.of (abPullback X))).Full :=
    Functor.Full.of_comp_faithful_iso
      (ExactFunctor.Derived.Plus.compιIso (ExactFunctor.of (abPullback X)))
  letI : (Adjunction.Derived.Plus.left (ExactFunctor.of (abPullback X))).Faithful :=
    Functor.Faithful.of_comp_iso
      (ExactFunctor.Derived.Plus.compιIso (ExactFunctor.of (abPullback X)))
  haveI : IsIso ((Adjunction.Derived.Plus.adjunction
      (ExactFunctor.of (abPullback X)) (abPushforward X) (abAdjunction X)).unit) :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  haveI : IsIso ((GrothendieckTopology.Derived.Plus.adjunction LCCat.zar_le_qc X).unit.app
      ((Adjunction.Derived.Plus.left (ExactFunctor.of (abPullback X))).obj K)) :=
    comparisonDerivedUnit_isIso X K
  rw [Adjunction.comp_unit_app]
  exact IsIso.comp_isIso'
    (NatIso.isIso_app_of_isIso _ K)
    (Functor.map_isIso (Adjunction.Derived.Plus.right (abPushforward X))
      ((GrothendieckTopology.Derived.Plus.adjunction LCCat.zar_le_qc X).unit.app
        ((Adjunction.Derived.Plus.left (ExactFunctor.of (abPullback X))).obj K)))

end CompositeUnit

/- Both declarations below are explicit functor/natural-transformation composites.  Their
`sorryAx` dependencies are inherited from canonical Prop-valued exactness and sheafification
owners, not from whole-data placeholders. -/

end LCCat.SmallToSlice

end
