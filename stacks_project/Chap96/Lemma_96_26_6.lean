/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.AffineFppf
import StacksCheckRecall

/-!
# Lemma 96.26.6

The comparison morphism `ε : 𝒳_affine,fppf ⟶ 𝒳_affine` satisfies the
assumptions and conclusions of Cohomology on Sites, Lemma 21.43.12.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ModulesOnCategory
open RingedSite RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)
variable [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u + 1} (affineFppfComparison X))
    (ModuleQis.{u + 1}
      (ofCommRingSheaf (affineSiteFppfTopology X) (affineFppfStructureSheaf X)))]
variable [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u + 1} (affineFppfComparison X))
    (ModuleQis.{u + 1} (ofCommRingSheaf ⊥ (affineStructureSheaf X)))]

/- Lemma 96.26.6: the affine fppf comparison satisfies the K-flat slice-sections
condition and induces the restricted derived equivalences. -/
@[stacks 0H0X]
#check (AlgebraicGeometry.GroupoidsOver.affineFppfComparison_spec X :
    (∀ (x : affineSite X)
      (M : CochainComplex (_root_.ModuleCat ((affineStructureSheaf X).obj.obj (Opposite.op x))) ℤ),
      M.IsKFlat → IsIso (TensorSections.comparison (affineStructureSheaf X).obj x
        (affineSiteFppfTopology X) (affineFppfStructureSheaf X)
        (((𝟭 (affineSite X)).sheafAdjunctionContinuous CommRingCat.{u + 1} ⊥
        (affineSiteFppfTopology X)).unit.app (affineStructureSheaf X)).hom M)) ∧
    (qcProperty X ≤ (affineFppfDerivedAdjunction X).unitIsoProperty) ∧
    (Adjunction.InverseImageRestriction.right (qcProperty X) :
      (affineFppfTargetProperty X).FullSubcategory ⥤
        (qcProperty X).FullSubcategory).IsEquivalence ∧
    (Adjunction.InverseImageRestriction.left (affineFppfDerivedAdjunction X)
      (qcProperty X) (affineFppfComparison_unitCondition X)).IsEquivalence)

end AlgebraicGeometry.GroupoidsOver
