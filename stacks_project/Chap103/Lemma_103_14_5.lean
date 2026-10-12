/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import stacks_project.Chap103.Lemma_103_14_4_LowerShriek

/-!
# Lower shriek of restricted structure sheaves

On an algebraic stack, module lower shriek of the restricted structure sheaf
along the lisse-étale and flat-fppf inclusions recovers `𝒪_X`. The
identification is the canonical `𝒪`-module adjunct of `𝒪' = g⁻¹ 𝒪`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

namespace lisseEtaleModuleLowerShriek

/-- The canonical `𝒪`-module homomorphism `g_! 𝒪' ⟶ 𝒪` adjoint to the
identification `𝒪' = g⁻¹ 𝒪` on the lisse-étale site. -/
def unitHom (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleModuleLowerShriek X).obj (SheafOfModules.unit (lisseEtaleStructureSheaf X)) ⟶
      SheafOfModules.unit (etaleStructureSheaf X) :=
  (homEquiv X (SheafOfModules.unit (lisseEtaleStructureSheaf X))
      (SheafOfModules.unit (etaleStructureSheaf X))).symm
    (SheafOfModules.unitToPushforwardObjUnit
      (𝟙 (lisseEtaleStructureSheaf X) :
        lisseEtaleStructureSheaf X ⟶
          ((lisseEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
            (lisseEtaleTopology X) X.etaleTopology).obj (etaleStructureSheaf X)))

/-- `unitHom` is the adjunct of the identity restriction `𝒪' ⟶ g_* 𝒪`. -/
theorem unitHom_homEquiv (X : GroupoidsOver S) [AlgebraicStack X] :
    homEquiv X (SheafOfModules.unit (lisseEtaleStructureSheaf X))
        (SheafOfModules.unit (etaleStructureSheaf X)) (unitHom X) =
      SheafOfModules.unitToPushforwardObjUnit
        (𝟙 (lisseEtaleStructureSheaf X) :
          lisseEtaleStructureSheaf X ⟶
            ((lisseEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
              (lisseEtaleTopology X) X.etaleTopology).obj (etaleStructureSheaf X)) :=
  sorry

/-- Lemma 103.14.5 (1): for an algebraic stack `X`, with `g` the lisse-étale
morphism of ringed topoi from Lemmas 103.14.2 and 103.14.4, one has
`g_! 𝒪_{X_lisse,étale} = 𝒪_X` as `𝒪_X`-modules, via the canonical adjunct of
`𝒪' = g⁻¹ 𝒪`. -/
@[stacks 078A, instance]
instance unitHom_isIso (X : GroupoidsOver S) [AlgebraicStack X] :
    IsIso (unitHom X) :=
  sorry

end lisseEtaleModuleLowerShriek

namespace flatFppfModuleLowerShriek

/-- The canonical `𝒪`-module homomorphism `g_! 𝒪' ⟶ 𝒪` adjoint to the
identification `𝒪' = g⁻¹ 𝒪` on the flat-fppf site. -/
def unitHom (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfModuleLowerShriek X).obj (SheafOfModules.unit (flatFppfStructureSheaf X)) ⟶
      SheafOfModules.unit (structureSheaf X) :=
  (homEquiv X (SheafOfModules.unit (flatFppfStructureSheaf X))
      (SheafOfModules.unit (structureSheaf X))).symm
    (SheafOfModules.unitToPushforwardObjUnit
      (𝟙 (flatFppfStructureSheaf X) :
        flatFppfStructureSheaf X ⟶
          ((flatFppfInclusion X).sheafPushforwardContinuous RingCat.{u}
            (flatFppfTopology X) (inheritedFppfTopology X)).obj (structureSheaf X)))

/-- `unitHom` is the adjunct of the identity restriction `𝒪' ⟶ g_* 𝒪`. -/
theorem unitHom_homEquiv (X : GroupoidsOver S) [AlgebraicStack X] :
    homEquiv X (SheafOfModules.unit (flatFppfStructureSheaf X))
        (SheafOfModules.unit (structureSheaf X)) (unitHom X) =
      SheafOfModules.unitToPushforwardObjUnit
        (𝟙 (flatFppfStructureSheaf X) :
          flatFppfStructureSheaf X ⟶
            ((flatFppfInclusion X).sheafPushforwardContinuous RingCat.{u}
              (flatFppfTopology X) (inheritedFppfTopology X)).obj (structureSheaf X)) :=
  sorry

/-- Lemma 103.14.5 (2): for an algebraic stack `X`, with `g` the flat-fppf
morphism of ringed topoi from Lemmas 103.14.2 and 103.14.4, one has
`g_! 𝒪_{X_flat,fppf} = 𝒪_X` as `𝒪_X`-modules, via the canonical adjunct of
`𝒪' = g⁻¹ 𝒪`. -/
@[stacks 078A, instance]
instance unitHom_isIso (X : GroupoidsOver S) [AlgebraicStack X] :
    IsIso (unitHom X) :=
  sorry

end flatFppfModuleLowerShriek

end AlgebraicGeometry.AlgebraicStack
