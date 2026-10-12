/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap87.Lemma_87_34_2_Pullback

/-!
# Morphisms of étale topoi of formal algebraic spaces

The morphism of sites `spacesEtalePullback f` induces a morphism of topoi of
étale sheaves of algebraic spaces over the reductions. Transport along
equation 87.34.1.1 yields the associated morphism of small étale topoi.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
variable [Reduction X] [Reduction Y]

/-- The morphism of topoi `Sh(X_spaces,étale) ⟶ Sh(Y_spaces,étale)` induced by
`spacesEtalePullback f`. -/
noncomputable abbrev spacesEtaleMorphismOfTopoi (f : X ⟶ Y) :
    MorphismOfTopoiIn (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  AlgebraicSpace.spacesEtaleMorphismOfTopoi (mapReduction f)

/-- `spacesEtaleMorphismOfTopoi f` is the algebraic-space spaces-étale topos
morphism of `mapReduction f`. -/
theorem spacesEtaleMorphismOfTopoi_eq (f : X ⟶ Y) :
    spacesEtaleMorphismOfTopoi f =
      AlgebraicSpace.spacesEtaleMorphismOfTopoi (mapReduction f) :=
  rfl

/-- The morphism of small étale topoi `f_small : Sh(X_étale) ⟶ Sh(Y_étale)`
obtained by transporting `spacesEtaleMorphismOfTopoi f` along 87.34.1.1. -/
noncomputable abbrev smallEtaleMorphismOfTopoi (f : X ⟶ Y) :
    MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X) :=
  AlgebraicSpace.smallEtaleMorphismOfTopoi (mapReduction f)

/-- `smallEtaleMorphismOfTopoi f` is the algebraic-space small étale topos
morphism of `mapReduction f`. -/
theorem smallEtaleMorphismOfTopoi_eq (f : X ⟶ Y) :
    smallEtaleMorphismOfTopoi f =
      AlgebraicSpace.smallEtaleMorphismOfTopoi (mapReduction f) :=
  rfl

variable {Z : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace Z] [Reduction Z]

/-- Inverse images of spaces étale topos morphisms compose up to the canonical
isomorphism of chosen fibre products of reductions. -/
noncomputable def spacesEtaleMorphismOfTopoiComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (AlgebraicSpace.spacesEtaleMorphismOfTopoi
        (mapReduction f ≫ mapReduction g)).inverseImage ≅
      ((spacesEtaleMorphismOfTopoi g).comp
        (spacesEtaleMorphismOfTopoi f)).inverseImage :=
  AlgebraicSpace.spacesEtaleMorphismOfTopoiComp (mapReduction f) (mapReduction g)

/-- `spacesEtaleMorphismOfTopoiComp f g` is algebraic-space spaces-étale topos
morphism composition along `mapReduction f` and `mapReduction g`. -/
theorem spacesEtaleMorphismOfTopoiComp_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtaleMorphismOfTopoiComp f g =
      AlgebraicSpace.spacesEtaleMorphismOfTopoiComp (mapReduction f)
        (mapReduction g) :=
  rfl

/-- Inverse images of small étale topos morphisms compose up to conjugation of
the spaces-étale comparison by 87.34.1.1. -/
noncomputable def smallEtaleMorphismOfTopoiComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (AlgebraicSpace.smallEtaleMorphismOfTopoi
        (mapReduction f ≫ mapReduction g)).inverseImage ≅
      ((smallEtaleMorphismOfTopoi g).comp
        (smallEtaleMorphismOfTopoi f)).inverseImage :=
  AlgebraicSpace.smallEtaleMorphismOfTopoiComp (mapReduction f) (mapReduction g)

/-- `smallEtaleMorphismOfTopoiComp f g` is algebraic-space small étale topos
morphism composition along `mapReduction f` and `mapReduction g`. -/
theorem smallEtaleMorphismOfTopoiComp_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleMorphismOfTopoiComp f g =
      AlgebraicSpace.smallEtaleMorphismOfTopoiComp (mapReduction f)
        (mapReduction g) :=
  rfl

end AlgebraicGeometry.FormalAlgebraicSpace
