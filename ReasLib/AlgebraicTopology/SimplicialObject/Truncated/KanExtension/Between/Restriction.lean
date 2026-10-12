/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.Between.Transfer
public import ReasLib.CategoryTheory.Functor.RightKanExtension.Transitivity
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction comparisons for truncated Kan extensions

This leaf compares chosen full coskeletons and skeletons with their restrictions to an
intermediate truncation level.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Truncated.Between

variable {C : Type u} [Category.{v} C]

namespace coskeleton.restriction

/-- The full coskeleton counit, restricted to an intermediate truncation level. -/
@[stacks 018B "restricted objectwise coskeleton counit"]
noncomputable def counit {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasCoskeleton] :
    (SimplexCategory.Truncated.incl n m h).op ⋙
        (SimplicialObject.truncation m).obj U.coskeleton ⟶ U :=
  (SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit U

/-- The componentwise comparison between the intermediate coskeleton and the restricted full
coskeleton, expressed entirely in canonical limit coordinates. -/
@[stacks 018B "componentwise intermediate coskeleton comparison"]
noncomputable def appIso {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasPointwiseCoskeleton]
    (Y : (SimplexCategory.Truncated m)ᵒᵖ) :
    (Between.coskeleton U m h).obj Y ≅
      ((SimplicialObject.truncation m).obj U.coskeleton).obj Y :=
  Functor.RightKanExtension.objIsoLimit
      (SimplexCategory.Truncated.incl n m h).op U Y ≪≫
    Limits.HasLimit.isoOfEquivalence
      (SimplexCategory.Truncated.incl.structuredArrowEquiv n m h Y)
      (Iso.refl _) ≪≫
    (Functor.RightKanExtension.objIsoLimit
      (SimplexCategory.Truncated.inclusion n).op U
      ((SimplexCategory.Truncated.inclusion m).op.obj Y)).symm

namespace appIso

/-- The limit-coordinate comparison is natural in the intermediate simplex. -/
@[stacks 018B "naturality of the componentwise coskeleton comparison"]
theorem naturality {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasPointwiseCoskeleton]
    {Y Z : (SimplexCategory.Truncated m)ᵒᵖ} (f : Y ⟶ Z) :
    (Between.coskeleton U m h).map f ≫ (appIso U m h Z).hom =
      (appIso U m h Y).hom ≫
        ((SimplicialObject.truncation m).obj U.coskeleton).map f := sorry

end appIso

/-- The chosen coskeleton between levels `n` and `m` agrees with the restriction of the full
`n`-coskeleton. -/
@[stacks 018B "comparison of intermediate and full coskeletons"]
noncomputable def iso {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasPointwiseCoskeleton] :
    Between.coskeleton U m h ≅
      (SimplicialObject.truncation m).obj U.coskeleton :=
  NatIso.ofComponents (fun Y ↦ appIso U m h Y)
    (fun f ↦ appIso.naturality U m h f)

/-- Restricting the full pointwise coskeleton to level `m` is a right Kan extension from
level `n` to level `m`. -/
@[stacks 018B "full coskeleton restricted between truncation levels"]
instance isRightKanExtension {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasPointwiseCoskeleton] :
    ((SimplicialObject.truncation m).obj U.coskeleton).IsRightKanExtension
      (counit U m h) := sorry

namespace iso

/-- The forward comparison from the intermediate coskeleton commutes with its counit. -/
@[reassoc (attr := simp), stacks 018B "intermediate coskeleton comparison on counits"]
theorem hom_counit {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasPointwiseCoskeleton] :
    Functor.whiskerLeft (SimplexCategory.Truncated.incl n m h).op
        (coskeleton.restriction.iso U m h).hom ≫
      coskeleton.restriction.counit U m h =
        Between.coskeleton.counit U m h := sorry

/-- The inverse comparison from the restricted full coskeleton commutes with its counit. -/
@[reassoc (attr := simp), stacks 018B "inverse intermediate coskeleton comparison on counits"]
theorem inv_counit {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasPointwiseCoskeleton] :
    Functor.whiskerLeft (SimplexCategory.Truncated.incl n m h).op
        (coskeleton.restriction.iso U m h).inv ≫
      Between.coskeleton.counit U m h =
        coskeleton.restriction.counit U m h := sorry

end iso

end coskeleton.restriction

namespace skeleton.restriction

/-- The full skeleton unit, restricted to an intermediate truncation level. -/
@[stacks 018N "restricted objectwise skeleton unit"]
noncomputable def unit {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasSkeleton] :
    U ⟶ (SimplexCategory.Truncated.incl n m h).op ⋙
      (SimplicialObject.truncation m).obj U.skeleton :=
  (SimplexCategory.Truncated.inclusion n).op.leftKanExtensionUnit U

/-- The componentwise comparison between the intermediate skeleton and the restricted full
skeleton, expressed entirely in canonical colimit coordinates. -/
@[stacks 018N "componentwise intermediate skeleton comparison"]
noncomputable def appIso {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasPointwiseSkeleton]
    (Y : (SimplexCategory.Truncated m)ᵒᵖ) :
    (Between.skeleton U m h).obj Y ≅
      ((SimplicialObject.truncation m).obj U.skeleton).obj Y :=
  (SimplexCategory.Truncated.incl n m h).op.leftKanExtensionObjIsoColimit U Y ≪≫
    Limits.HasColimit.isoOfEquivalence
      (SimplexCategory.Truncated.incl.costructuredArrowEquiv n m h Y)
      (Iso.refl _) ≪≫
    ((SimplexCategory.Truncated.inclusion n).op.leftKanExtensionObjIsoColimit U
      ((SimplexCategory.Truncated.inclusion m).op.obj Y)).symm

namespace appIso

/-- The colimit-coordinate comparison is natural in the intermediate simplex. -/
@[stacks 018N "naturality of the componentwise skeleton comparison"]
theorem naturality {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasPointwiseSkeleton]
    {Y Z : (SimplexCategory.Truncated m)ᵒᵖ} (f : Y ⟶ Z) :
    (Between.skeleton U m h).map f ≫ (appIso U m h Z).hom =
      (appIso U m h Y).hom ≫
        ((SimplicialObject.truncation m).obj U.skeleton).map f := sorry

end appIso

/-- The chosen skeleton between levels `n` and `m` agrees with the restriction of the full
`n`-skeleton. -/
@[stacks 018N "comparison of intermediate and full skeletons"]
noncomputable def iso {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasPointwiseSkeleton] :
    Between.skeleton U m h ≅
      (SimplicialObject.truncation m).obj U.skeleton :=
  NatIso.ofComponents (fun Y ↦ appIso U m h Y)
    (fun f ↦ appIso.naturality U m h f)

/-- Restricting the full pointwise skeleton to level `m` is a left Kan extension from level `n`
to level `m`. -/
@[stacks 018N "full skeleton restricted between truncation levels"]
instance isLeftKanExtension {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasPointwiseSkeleton] :
    ((SimplicialObject.truncation m).obj U.skeleton).IsLeftKanExtension
      (unit U m h) := sorry

namespace iso

/-- The forward comparison from the intermediate skeleton commutes with its unit. -/
@[reassoc (attr := simp), stacks 018N "intermediate skeleton comparison on units"]
theorem unit_hom {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasPointwiseSkeleton] :
    Between.skeleton.unit U m h ≫
      Functor.whiskerLeft (SimplexCategory.Truncated.incl n m h).op
        (skeleton.restriction.iso U m h).hom =
          skeleton.restriction.unit U m h := sorry

/-- The inverse comparison from the restricted full skeleton commutes with its unit. -/
@[reassoc (attr := simp), stacks 018N "inverse intermediate skeleton comparison on units"]
theorem unit_inv {n : ℕ} (U : SimplicialObject.Truncated C n)
    (m : ℕ) (h : n ≤ m) [U.HasPointwiseSkeleton] :
    skeleton.restriction.unit U m h ≫
      Functor.whiskerLeft (SimplexCategory.Truncated.incl n m h).op
        (skeleton.restriction.iso U m h).inv =
          Between.skeleton.unit U m h := sorry

end iso

end skeleton.restriction

end CategoryTheory.SimplicialObject.Truncated.Between
