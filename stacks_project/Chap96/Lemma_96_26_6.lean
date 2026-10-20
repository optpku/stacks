module

public import stacks_project.Chap96.Lemma_96_26_6_Comparison
import Mathlib.Tactic.CrossRefAttribute

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
variable [HasWeakSheafify (affineSiteFppfTopology X) CommRingCat.{u + 1}]
variable [∀ P : (affineSite X)ᵒᵖ ⥤ CommRingCat.{u + 1},
    (𝟭 (affineSite X)).op.HasLeftKanExtension P]
variable [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u + 1} (affineFppfComparison X))
    (ModuleQis.{u + 1}
      (ofCommRingSheaf (affineSiteFppfTopology X) (affineFppfStructureSheaf X)))]
variable [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u + 1} (affineFppfComparison X))
    (ModuleQis.{u + 1} (ofCommRingSheaf ⊥ (affineStructureSheaf X)))]

/-- Lemma 96.26.6 (1): the comparison morphism
`ε : 𝒳_affine,fppf ⟶ 𝒳_affine` satisfies the K-flat sections unit
condition of Cohomology on Sites, Lemma 21.43.12. -/
@[stacks 0H0X]
theorem affineFppfComparison_unitCondition :
    qcProperty X ≤ (affineFppfDerivedAdjunction X).unitIsoProperty :=
  sorry

/-- Lemma 96.26.6 (2): restriction of `Rε_*` to objects whose derived
pushforward lies in `QC(𝒳)` is an equivalence onto `QC(𝒳)`. -/
@[stacks 0H0X, instance]
instance affineFppfComparison_pushforwardRestriction_isEquivalence :
    (Adjunction.InverseImageRestriction.right (qcProperty X) :
        (affineFppfTargetProperty X).FullSubcategory ⥤
          (qcProperty X).FullSubcategory).IsEquivalence :=
  sorry

/-- Lemma 96.26.6 (3): restriction of `ε^*` is the mutually quasi-inverse
equivalence of Cohomology on Sites, Lemma 21.43.12. -/
@[stacks 0H0X, instance]
instance affineFppfComparison_pullbackRestriction_isEquivalence :
    (Adjunction.InverseImageRestriction.left (affineFppfDerivedAdjunction X)
      (qcProperty X) (affineFppfComparison_unitCondition X)).IsEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidsOver
