/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_33_1_Comparison
public import stacks_project.Chap85.Lemma_85_33_1_Etale
public import stacks_project.Chap85.Lemma_85_36_1_Comparison

/-!
# Lemma 85.36.1

The ph-to-étale comparison morphisms of a simplicial algebraic space and an
augmentation assemble to a commutative square of topoi.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.SimplicialObject
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}}

/-- Lemma 85.36.1. Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S`, and `a : U ⟶ X` an augmentation. There is a
commutative diagram of topoi
`Sh (sliceTotalTopology (phTopology S) U) ⟶ Sh (spacesEtaleTotalTopology U)` over
`Sh (bigPhSite X) ⟶ Sh (spacesEtaleTopology X)`, whose left vertical arrow is the
Section 85.21 slice augmentation and whose right vertical arrow is the
Section 85.32 étale augmentation. -/
@[stacks 0DHJ]
def phEtaleAugmentationInverseImageIso (X : AlgebraicSpace S)
    (U : SimplicialObject (AlgebraicSpace S))
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (spacesEtaleAugmentation U a)⁻¹ ⋙ (phEtaleComparison U)⁻¹ ≅
      (spacesPhComparison X)⁻¹ ⋙ (phAugmentation U a)⁻¹ :=
  Adjunction.leftAdjointCompIso
    ((augmentationFunctor U a).sheafAdjunctionContinuous (Type (u + 1))
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U))
    ((toSliceTotal U).sheafAdjunctionContinuous (Type (u + 1))
      (spacesEtaleTotalTopology U) (sliceTotalTopology (phTopology S) U))
    (((Etale.SmallToBig.spacesEtaleToBig X).sheafAdjunctionContinuous (Type (u + 1))
        (spacesEtaleTopology X) (bigPhSite X)).comp
      ((sliceAugmentationPullback U a).sheafAdjunctionContinuous (Type (u + 1))
        (bigPhSite X) (sliceTotalTopology (phTopology S) U)))
    (Functor.sheafPushforwardContinuousComp' (presentingCommSq U a) (Type (u + 1))
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U)
      (sliceTotalTopology (phTopology S) U))

/-- The inverse-image square of Lemma 85.36.1 has sides
`spacesEtaleAugmentation` (right vertical `a`), `phEtaleComparison` (top `h`),
`spacesPhComparison` (bottom `h₋₁`), and `phAugmentation` (left vertical `a_ph`). -/
def phEtaleAugmentationInverseImageIso_spec (X : AlgebraicSpace S)
    (U : SimplicialObject (AlgebraicSpace S))
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (spacesEtaleAugmentation U a)⁻¹ ⋙ (phEtaleComparison U)⁻¹ ≅
      (spacesPhComparison X)⁻¹ ⋙ (phAugmentation U a)⁻¹ :=
  phEtaleAugmentationInverseImageIso X U a

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
