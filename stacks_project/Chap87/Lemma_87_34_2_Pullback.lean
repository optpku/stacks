/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap87.Definition_87_34_1_Site

/-!
# Pullback on étale sites of formal algebraic spaces

A morphism of formal algebraic spaces induces the base-change functor on the
étale sites of algebraic spaces of its reductions, as the algebraic-space
pullback of `mapReduction`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
variable [Reduction X] [Reduction Y]

/-- Base change along `f` on the étale sites of algebraic spaces over the
reductions, sending `V` to `X_red ×_{Y_red} V`. -/
noncomputable abbrev spacesEtalePullback (f : X ⟶ Y) :
    spacesEtaleSite Y ⥤ spacesEtaleSite X :=
  AlgebraicSpace.spacesEtalePullback (mapReduction f)

/-- `spacesEtalePullback f` is algebraic-space étale pullback along
`mapReduction f`. -/
theorem spacesEtalePullback_eq (f : X ⟶ Y) :
    spacesEtalePullback f = AlgebraicSpace.spacesEtalePullback (mapReduction f) :=
  rfl

/-- Base change along `f` is continuous for the étale topologies of algebraic
spaces over the reductions. -/
instance spacesEtalePullback_isContinuous (f : X ⟶ Y) :
    (spacesEtalePullback f).IsContinuous (spacesEtaleTopology Y)
      (spacesEtaleTopology X) :=
  AlgebraicSpace.spacesEtalePullback_isContinuous (mapReduction f)

/-- Base change along `f` is a morphism of étale sites of algebraic spaces over
the reductions. -/
instance spacesEtalePullback_isMorphismOfSites (f : X ⟶ Y) :
    IsMorphismOfSites (spacesEtaleTopology Y) (spacesEtaleTopology X)
      (spacesEtalePullback f) :=
  AlgebraicSpace.spacesEtalePullback_isMorphismOfSites (mapReduction f)

variable {Z : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace Z] [Reduction Z]

/-- Base change along a composite of reduction maps is the composite of the
base-change functors, up to the canonical isomorphism of chosen fibre products. -/
noncomputable def spacesEtalePullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    AlgebraicSpace.spacesEtalePullback (mapReduction f ≫ mapReduction g) ≅
      spacesEtalePullback g ⋙ spacesEtalePullback f :=
  AlgebraicSpace.spacesEtalePullbackComp (mapReduction f) (mapReduction g)

/-- `spacesEtalePullbackComp f g` is algebraic-space étale pullback composition
along `mapReduction f` and `mapReduction g`. -/
theorem spacesEtalePullbackComp_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtalePullbackComp f g =
      AlgebraicSpace.spacesEtalePullbackComp (mapReduction f) (mapReduction g) :=
  rfl

end AlgebraicGeometry.FormalAlgebraicSpace
