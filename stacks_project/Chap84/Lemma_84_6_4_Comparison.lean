/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import stacks_project.Chap73.Lemma_73_7_8_Big
public import stacks_project.Chap84.Lemma_84_8_4_Comparison

/-!
# Fppf and étale comparisons of algebraic-space topoi

This leaf names the identity-on-objects comparison `ε` from `(Spaces/X)_fppf`
to `(Spaces/X)_étale` and the composite `a = π ∘ ε` with the imported
small-to-big étale relocalization `π`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The localized big fppf topology on `Over X`, i.e. `(Spaces/X)_fppf`. -/
abbrev overFppfTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    GrothendieckTopology (Over X) :=
  (fppfTopology S).over X

/-- `overFppfTopology X` is the localization of `fppfTopology S` at `X`. -/
theorem overFppfTopology_def {S : Scheme.{u}} (X : AlgebraicSpace S) :
    overFppfTopology X = (fppfTopology S).over X := sorry

namespace Fppf

variable {S : Scheme.{u}}

/-- The identity functor of `Over X` is a morphism of sites from
`(Spaces/X)_fppf` to `(Spaces/X)_étale`. -/
instance epsilon_isMorphismOfSites (X : AlgebraicSpace S) :
    IsMorphismOfSites
      (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)
      (overFppfTopology X) (𝟭 (Over X)) :=
  sorry

/-- Identity pullback from the big fppf site of `X` to the big étale site
preserves finite limits. -/
instance epsilon_sheafPullback_preservesFiniteLimits (X : AlgebraicSpace S) :
    PreservesFiniteLimits
      ((𝟭 (Over X)).sheafPullback (Type (u + 1))
        (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)
        (overFppfTopology X)) :=
  sorry

/-- The opposite identity functor admits left Kan extensions of type-valued
presheaves. -/
instance epsilon_op_hasLeftKanExtension (X : AlgebraicSpace S)
    (P : (Over X)ᵒᵖ ⥤ Type (u + 1)) :
    (𝟭 (Over X)).op.HasLeftKanExtension P :=
  sorry

/-- The morphism of topoi `ε_X : Sh((Spaces/X)_fppf) ⟶ Sh((Spaces/X)_étale)`
induced by the identity functor of `Over X`. -/
def epsilon (X : AlgebraicSpace S) :
    MorphismOfTopoiIn
      (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)
      (overFppfTopology X) :=
  (IsMorphismOfSites.toMorphismOfTopoiIn (𝟭 (Over X)) :
    LeftExactAdjunction
      (Sheaf (overFppfTopology X) (Type (u + 1)))
      (Sheaf (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)
        (Type (u + 1))))

/-- Direct image along `epsilon X` is continuous sheaf pushforward of the
identity functor. -/
theorem epsilon_pushforward (X : AlgebraicSpace S) :
    (epsilon X).pushforward =
      (𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1))
        (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)
        (overFppfTopology X) :=
  sorry

/-- Inverse image along `epsilon X` is sheaf pullback of the identity functor. -/
theorem epsilon_inverseImage (X : AlgebraicSpace S) :
    (epsilon X)⁻¹ =
      (𝟭 (Over X)).sheafPullback (Type (u + 1))
        (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)
        (overFppfTopology X) :=
  sorry

end Fppf

namespace Etale.SmallToBig

variable {S : Scheme.{u}}

/-- The morphism of topoi `a_X = π_X ∘ ε_X` from the big fppf topos of `X` to
the small étale topos of `X`. -/
def fppfComparison (X : AlgebraicSpace S) :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (overFppfTopology X) :=
  MorphismOfTopoiIn.comp (siteMorphismOfTopoi X) (Fppf.epsilon X)

/-- `fppfComparison X` is the composite `π_X ∘ ε_X`. -/
theorem fppfComparison_eq_comp (X : AlgebraicSpace S) :
    fppfComparison X =
      MorphismOfTopoiIn.comp (siteMorphismOfTopoi X) (Fppf.epsilon X) :=
  sorry

/-- Direct image along `fppfComparison X` is the composite of the direct images
of `ε_X` and `π_X`. -/
theorem fppfComparison_pushforward (X : AlgebraicSpace S) :
    (fppfComparison X).pushforward =
      (Fppf.epsilon X).pushforward ⋙ (siteMorphismOfTopoi X).pushforward :=
  sorry

variable {X Y : AlgebraicSpace S}

/-- The morphism of small étale topoi `f_small` associated to a morphism of
algebraic spaces, at coefficients `Type (u + 1)`. -/
abbrev smallMorphism (f : X ⟶ Y) :
    MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X) :=
  smallEtaleMorphismOfTopoi f

/-- `smallMorphism f` is the Type `(u + 1)` small étale morphism of topoi. -/
theorem smallMorphism_eq (f : X ⟶ Y) :
    smallMorphism f = smallEtaleMorphismOfTopoi f :=
  sorry

end Etale.SmallToBig

end AlgebraicGeometry.AlgebraicSpace

end

end
