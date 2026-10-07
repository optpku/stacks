module

public import ReasLib.Topology.Category.LCCat.SmallToSlice.Comparison
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Consequences
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
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
    IsIso (qcPushforward_aInverse_unit X F) := sorry

variable [HasInjectiveResolutions
  (Sheaf (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1})]

/-- Positive direct images of `a_X⁻¹ F` vanish. -/
@[stacks 0DCY "higher direct-image vanishing for a_X⁻¹"]
theorem qcPushforward_aInverse_higherDirectImage_isZero
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})
    (i : ℕ) (hi : 0 < i) :
    IsZero
      (((comparisonTopologyPushforwardAb LCCat.zar_le_qc X).rightDerived i).obj
        ((aInverseAb X).obj F)) := sorry

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
            ((aInverseAb X).obj F)) := sorry

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
        ((abPullbackPlus X).obj K)) := sorry

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
        (GrothendieckTopology.Derived.Plus.adjunction LCCat.zar_le_qc X)).unit).app K) := sorry

end CompositeUnit

/- Both declarations below are explicit functor/natural-transformation composites.  Their
`sorryAx` dependencies are inherited from canonical Prop-valued exactness and sheafification
owners, not from whole-data placeholders. -/

end LCCat.SmallToSlice

end
