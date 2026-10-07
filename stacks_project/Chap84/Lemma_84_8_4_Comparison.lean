module

public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap73.Lemma_73_8_8_Big
public import stacks_project.Chap84.Lemma_84_5_2_Relocalization
public import stacks_project.Chap84.Lemma_84_8_4_Big

/-!
# Ph to étale comparison morphisms of topoi on algebraic spaces

This leaf owns the comparison maps `ε`, `π`, and `a = π ∘ ε` relating the big
ph topos of an algebraic space to its big and small étale topoi, together with
the two commutative squares of topoi for a morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u w

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The big étale slice topology is coarser than the big ph slice topology. -/
theorem overEtaleTopology_le_bigPhSite (X : AlgebraicSpace S) :
    overEtaleTopology X ≤ bigPhSite X := sorry

/-- The identity on `Over X` is continuous from `(Spaces/X)_étale` to
`(Spaces/X)_ph`. -/
instance identity_etale_isContinuous_ph (X : AlgebraicSpace S) :
    Functor.IsContinuous (𝟭 (Over X)) (overEtaleTopology X) (bigPhSite X) := sorry

/-- The identity on `Over X` is a morphism of sites from `(Spaces/X)_ph` to
`(Spaces/X)_étale`. -/
instance identity_etale_isMorphismOfSites_ph (X : AlgebraicSpace S) :
    IsMorphismOfSites (overEtaleTopology X) (bigPhSite X) (𝟭 (Over X)) := sorry

/-- The opposite identity functor admits left Kan extensions of type-valued
presheaves. -/
instance identity_op_hasLeftKanExtension (X : AlgebraicSpace S)
    (P : (Over X)ᵒᵖ ⥤ Type (u + 1)) :
    (𝟭 (Over X)).op.HasLeftKanExtension P := sorry

/-- Sheaf pullback along the identity from the étale slice topology to the ph
slice topology preserves finite limits. -/
instance identity_etale_ph_sheafPullback_preservesFiniteLimits (X : AlgebraicSpace S) :
    PreservesFiniteLimits
      ((𝟭 (Over X)).sheafPullback (Type (u + 1))
        (overEtaleTopology X) (bigPhSite X)) := sorry

namespace Etale.SmallToBig

/-- Relocalization along `𝟙 X` is continuous into the root big étale slice
topology `(Spaces/X)_étale`. -/
instance relocalizationFunctor_id_isContinuous (X : AlgebraicSpace S) :
    Functor.IsContinuous (relocalizationFunctor (𝟙 X)) (smallEtaleTopology X)
      (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X) := sorry

/-- Relocalization along `𝟙 X` admits left Kan extensions of type-valued
presheaves. -/
instance relocalizationFunctor_id_op_hasLeftKanExtension (X : AlgebraicSpace S)
    (P : (smallEtaleSite X)ᵒᵖ ⥤ Type w) :
    (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P := sorry

/-- Sheaf pullback along relocalization of `𝟙 X` preserves finite limits. -/
instance relocalizationFunctor_id_sheafPullback_preservesFiniteLimits
    (X : AlgebraicSpace S) :
    PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 X)).sheafPullback.{u + 1, u, u + 1, u + 2, u + 1, u + 1}
        (Type (u + 1)) (smallEtaleTopology X)
        (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)) := sorry

/-- The morphism of topoi `π_X : Sh((Spaces/X)_étale) ⟶ Sh(X_étale)` induced by
small-to-big étale relocalization along `𝟙 X`. -/
def siteMorphismOfTopoi (X : AlgebraicSpace S) :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X)
      (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X) :=
  Functor.morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u, u + 1}
    (relocalizationFunctor (𝟙 X)) (smallEtaleTopology X)
    (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)

/-- `siteMorphismOfTopoi X` is the topos morphism of relocalization along `𝟙 X`. -/
theorem siteMorphismOfTopoi_eq (X : AlgebraicSpace S) :
    siteMorphismOfTopoi X =
      Functor.morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u, u + 1}
        (relocalizationFunctor (𝟙 X)) (smallEtaleTopology X)
        (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X) :=
  sorry

end Etale.SmallToBig

namespace PhComparison

/-- The comparison morphism of topoi `ε_X : Sh((Spaces/X)_ph) ⟶ Sh((Spaces/X)_étale)`
induced by the identity site functor. -/
def epsilon (X : AlgebraicSpace S) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (overEtaleTopology X) (bigPhSite X) :=
  ((𝟭 (Over X)).morphismOfTopoiInOfContinuous (overEtaleTopology X) (bigPhSite X) :
    LeftExactAdjunction
      (Sheaf (bigPhSite X) (Type (u + 1)))
      (Sheaf (overEtaleTopology X) (Type (u + 1))))

/-- `epsilon X` is the topos morphism of the identity site functor from
`(Spaces/X)_étale` to `(Spaces/X)_ph`. -/
theorem epsilon_eq (X : AlgebraicSpace S) :
    epsilon X =
      (𝟭 (Over X)).morphismOfTopoiInOfContinuous (overEtaleTopology X) (bigPhSite X) :=
  sorry

/-- The inverse-image projection of `epsilon`. -/
@[simp]
theorem epsilon_inverseImage (X : AlgebraicSpace S) :
    (epsilon X)⁻¹ =
      (𝟭 (Over X)).sheafPullback (Type (u + 1))
        (overEtaleTopology X) (bigPhSite X) :=
  sorry

/-- The direct-image projection of `epsilon`. -/
@[simp]
theorem epsilon_pushforward (X : AlgebraicSpace S) :
    (epsilon X).pushforward =
      (𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1))
        (overEtaleTopology X) (bigPhSite X) :=
  sorry

/-- The composite comparison `a_X = π_X ∘ ε_X` from the big ph topos to the
small étale topos. -/
def toSmallEtale (X : AlgebraicSpace S) :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (bigPhSite X) :=
  MorphismOfTopoiIn.comp (Etale.SmallToBig.siteMorphismOfTopoi X) (epsilon X)

/-- The source identification `a_X = π_X ∘ ε_X`. -/
theorem toSmallEtale_eq_comp (X : AlgebraicSpace S) :
    toSmallEtale X =
      MorphismOfTopoiIn.comp (Etale.SmallToBig.siteMorphismOfTopoi X) (epsilon X) :=
  sorry

variable {X Y : AlgebraicSpace S}

/-- Direct image along `f_big,ph` and `f_big,étale` form a commutative square
with the identity comparisons `ε_X` and `ε_Y`. -/
theorem bigPhEtaleCommSq (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (Ph.Big.morphismOfTopoi f).pushforward
      (epsilon X).pushforward
      (epsilon Y).pushforward
      (Etale.Big.morphismOfTopoi f).pushforward) :=
  sorry

/-- Direct image along `f_big,ph` and `f_small` form a commutative square with
`a_X = π_X ∘ ε_X` and `a_Y = π_Y ∘ ε_Y`. -/
theorem phSmallEtaleCommSq (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (Ph.Big.morphismOfTopoi f).pushforward
      (toSmallEtale X).pushforward
      (toSmallEtale Y).pushforward
      (smallEtaleMorphismOfTopoi f).pushforward) :=
  sorry

end PhComparison

end AlgebraicGeometry.AlgebraicSpace

end

end
