module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.AffineEtale
import StacksCheckRecall

/-!
# Lemma 96.26.3

The comparison morphism `ε : 𝒳_affine,étale ⟶ 𝒳_affine` satisfies the
assumptions and conclusions of Cohomology on Sites, Lemma 21.43.12.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ModulesOnCategory
open RingedSite RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)
variable [HasWeakSheafify (affineSiteEtaleTopology X) CommRingCat.{u + 1}]
variable [∀ P : (affineSite X)ᵒᵖ ⥤ CommRingCat.{u + 1},
    (𝟭 (affineSite X)).op.HasLeftKanExtension P]
variable [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u + 1} (affineEtaleComparison X))
    (ModuleQis.{u + 1}
      (ofCommRingSheaf (affineSiteEtaleTopology X) (affineEtaleStructureSheaf X)))]
variable [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u + 1} (affineEtaleComparison X))
    (ModuleQis.{u + 1} (ofCommRingSheaf ⊥ (affineStructureSheaf X)))]

/- Lemma 96.26.3: the affine étale comparison satisfies the K-flat slice-sections
hypothesis and the derived conclusions of the comparison theorem. -/
@[stacks 0H0J] #check (AlgebraicGeometry.GroupoidsOver.affineEtaleComparison_spec X :
    (∀ (x : affineSite X)
      (M : CochainComplex (_root_.ModuleCat ((affineStructureSheaf X).obj.obj (Opposite.op x))) ℤ),
      M.IsKFlat → IsIso (TensorSections.comparison (affineStructureSheaf X).obj x
        (affineSiteEtaleTopology X) (affineEtaleStructureSheaf X)
        (((𝟭 (affineSite X)).sheafAdjunctionContinuous CommRingCat.{u + 1} ⊥
          (affineSiteEtaleTopology X)).unit.app (affineStructureSheaf X)).hom M)) ∧
    (qcProperty X ≤ (affineEtaleDerivedAdjunction X).unitIsoProperty) ∧
    (Adjunction.InverseImageRestriction.right (qcProperty X) :
      (affineEtaleTargetProperty X).FullSubcategory ⥤
        (qcProperty X).FullSubcategory).IsEquivalence ∧
    (Adjunction.InverseImageRestriction.left (affineEtaleDerivedAdjunction X)
      (qcProperty X) (affineEtaleComparison_unitCondition X)).IsEquivalence)

#check (AlgebraicGeometry.GroupoidsOver.affineEtaleComparison_unitCondition X :
  qcProperty X ≤ (affineEtaleDerivedAdjunction X).unitIsoProperty)

#check (AlgebraicGeometry.GroupoidsOver.affineEtaleComparison_pushforwardRestriction_isEquivalence X :
  (Adjunction.InverseImageRestriction.right (qcProperty X) :
    (affineEtaleTargetProperty X).FullSubcategory ⥤
      (qcProperty X).FullSubcategory).IsEquivalence)

#check (AlgebraicGeometry.GroupoidsOver.affineEtaleComparison_pullbackRestriction_isEquivalence X :
  (Adjunction.InverseImageRestriction.left (affineEtaleDerivedAdjunction X)
    (qcProperty X) (affineEtaleComparison_unitCondition X)).IsEquivalence)

end AlgebraicGeometry.GroupoidsOver
