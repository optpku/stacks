module

public import stacks_project.Chap85.Lemma_85_33_1_Comparison
public import stacks_project.Chap85.Lemma_85_33_1_Etale

/-!
# Ph–étale comparison morphisms for a simplicial algebraic space

The identity-on-objects inclusion of the spaces-étale total site into the ph
total site, together with the Case A augmentations of `U` and `X`, present
morphisms of topoi `h`, `h₋₁`, and `a_ph` for the commutative square of
Lemma 85.36.1.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.SimplicialObject
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- The inclusion `SpacesEtale U ⥤ sliceTotalSite U` is continuous for the total
spaces-étale and ph topologies. -/
instance toSliceTotal_isContinuous_ph :
    (toSliceTotal U).IsContinuous (spacesEtaleTotalTopology U)
      (sliceTotalTopology (phTopology S) U) :=
  sorry

/-- Sheaves of types in universe `u + 1` on `(Spaces/U)_{ph,total}` admit
sheafification. -/
instance hasSheafify_sliceTotalTopology_ph :
    HasSheafify (sliceTotalTopology (phTopology S) U) (Type (u + 1)) :=
  sorry

/-- Sheaf pullback along `toSliceTotal U` into the ph total topos preserves
finite limits. -/
instance toSliceTotal_sheafPullback_preservesFiniteLimits_ph :
    PreservesFiniteLimits
      ((toSliceTotal U).sheafPullback (Type (u + 1))
        (spacesEtaleTotalTopology U) (sliceTotalTopology (phTopology S) U)) :=
  sorry

/-- The top horizontal morphism of topoi
`h : Sh((Spaces/U)_{ph,total}) ⟶ Sh(U_spaces,étale)` presented by
`toSliceTotal`. -/
def phEtaleComparison :
    MorphismOfTopoiIn (spacesEtaleTotalTopology U)
      (sliceTotalTopology (phTopology S) U) :=
  (toSliceTotal U).morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1}
    (spacesEtaleTotalTopology U) (sliceTotalTopology (phTopology S) U)

/-- Inverse image of `phEtaleComparison U` is sheaf pullback along
`toSliceTotal U`. -/
theorem phEtaleComparison_inverseImage :
    (phEtaleComparison U)⁻¹ =
      (toSliceTotal U).sheafPullback (Type (u + 1))
        (spacesEtaleTotalTopology U) (sliceTotalTopology (phTopology S) U) :=
  sorry

variable (X : AlgebraicSpace S)

/-- The forgetful functor `X_spaces,étale ⥤ (Spaces/X)_ph` is continuous. -/
instance spacesEtaleToBig_isContinuous_ph :
    (Etale.SmallToBig.spacesEtaleToBig X).IsContinuous
      (spacesEtaleTopology X) (bigPhSite X) :=
  sorry

/-- Sheaf pullback along `spacesEtaleToBig X` into the big ph topos preserves
finite limits. -/
instance spacesEtaleToBig_sheafPullback_preservesFiniteLimits_ph :
    PreservesFiniteLimits
      ((Etale.SmallToBig.spacesEtaleToBig X).sheafPullback (Type (u + 1))
        (spacesEtaleTopology X) (bigPhSite X)) :=
  sorry

/-- Sheaf pullback along `spacesEtaleToBig X` into `(Spaces/X)_étale` preserves
finite limits. -/
instance spacesEtaleToBig_sheafPullback_preservesFiniteLimits_etale :
    PreservesFiniteLimits
      ((Etale.SmallToBig.spacesEtaleToBig X).sheafPullback (Type (u + 1))
        (spacesEtaleTopology X) (overEtaleTopology X)) :=
  sorry

/-- The bottom horizontal morphism of topoi
`h₋₁ : Sh((Spaces/X)_ph) ⟶ Sh(X_spaces,étale)` presented by `U ↦ U / X`.
This is the spaces-étale form of `a_X = π_X ∘ ε_X`. -/
def spacesPhComparison :
    MorphismOfTopoiIn (spacesEtaleTopology X) (bigPhSite X) :=
  (Etale.SmallToBig.spacesEtaleToBig X).morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1}
    (spacesEtaleTopology X) (bigPhSite X)

/-- Inverse image of `spacesPhComparison X` is sheaf pullback along
`spacesEtaleToBig X`. -/
theorem spacesPhComparison_inverseImage :
    (spacesPhComparison X)⁻¹ =
      (Etale.SmallToBig.spacesEtaleToBig X).sheafPullback (Type (u + 1))
        (spacesEtaleTopology X) (bigPhSite X) :=
  sorry

/-- Inverse image of `spacesPhComparison X` is isomorphic to `π⁻¹ ⋙ ε⁻¹`,
where `π` is the spaces-étale-to-big-étale morphism presented by
`spacesEtaleToBig` and `ε` is `PhComparison.epsilon`. -/
def spacesPhComparison_inverseImage_compIso :
    (spacesPhComparison X)⁻¹ ≅
      ((Etale.SmallToBig.spacesEtaleToBig X).morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1}
          (spacesEtaleTopology X) (overEtaleTopology X))⁻¹ ⋙
        (PhComparison.epsilon X)⁻¹ :=
  (Functor.sheafPullbackComp' (spacesEtaleTopology X) (overEtaleTopology X)
      (bigPhSite X) (Etale.SmallToBig.spacesEtaleToBig X) (𝟭 (Over X))
      (Functor.rightUnitor (Etale.SmallToBig.spacesEtaleToBig X))).symm

variable {X : AlgebraicSpace S} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- Sheaf pullback along `sliceAugmentationPullback` into the ph total topos
preserves finite limits. -/
instance sliceAugmentationPullback_sheafPullback_preservesFiniteLimits_ph :
    PreservesFiniteLimits
      ((sliceAugmentationPullback U a).sheafPullback (Type (u + 1))
        (bigPhSite X) (sliceTotalTopology (phTopology S) U)) :=
  sorry

/-- The left vertical morphism of topoi
`a_ph : Sh((Spaces/U)_{ph,total}) ⟶ Sh((Spaces/X)_ph)`, presented by the
Case A continuous functor of Section 85.21. -/
def phAugmentation :
    MorphismOfTopoiIn (bigPhSite X) (sliceTotalTopology (phTopology S) U) :=
  (sliceAugmentationPullback U a).morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1}
    (bigPhSite X) (sliceTotalTopology (phTopology S) U)

/-- Inverse image of `phAugmentation a` is sheaf pullback along
`sliceAugmentationPullback`. -/
theorem phAugmentation_eq :
    (phAugmentation U a)⁻¹ =
      (sliceAugmentationPullback U a).sheafPullback (Type (u + 1))
        (bigPhSite X) (sliceTotalTopology (phTopology S) U) :=
  sorry

/-- The left presenting composite of the source square is continuous for the ph
total topology. -/
instance augmentationFunctor_comp_toSliceTotal_isContinuous_ph :
    (augmentationFunctor U a ⋙ toSliceTotal U).IsContinuous
      (spacesEtaleTopology X) (sliceTotalTopology (phTopology S) U) :=
  sorry

/-- The right presenting composite of the source square is continuous for the ph
total topology. -/
instance spacesEtaleToBig_comp_sliceAugmentationPullback_isContinuous_ph :
    (Etale.SmallToBig.spacesEtaleToBig X ⋙ sliceAugmentationPullback U a).IsContinuous
      (spacesEtaleTopology X) (sliceTotalTopology (phTopology S) U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
