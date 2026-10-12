/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Pullback on the spaces-étale site

A morphism of algebraic spaces induces the base-change functor `V ↦ X ×_Y V` on the
étale sites of algebraic spaces, as `MorphismProperty.Over.pullback`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.MorphismProperty
open AlgebraicGeometry.AlgebraicSpace.ReasLibPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Fibre products of algebraic spaces over a scheme exist. -/
instance instHasPullbacks_algebraicSpace : HasPullbacks (AlgebraicSpace S) :=
  ReasLibPullback.instHasPullbacks

/-- Étale morphisms of algebraic spaces are stable under base change. -/
instance instIsStableUnderBaseChange_etale :
    IsStableUnderBaseChange (@Etale S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- Base change along `f` on the étale sites of algebraic spaces, sending `V` to `X ×_Y V`. -/
noncomputable abbrev spacesEtalePullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    spacesEtaleSite Y ⥤ spacesEtaleSite X :=
  MorphismProperty.Over.pullback (@Etale S) ⊤ f

/-- Base change along a composite is the composite of the base-change functors, up to the
canonical isomorphism of chosen fibre products. -/
noncomputable def spacesEtalePullbackComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtalePullback (f ≫ g) ≅ spacesEtalePullback g ⋙ spacesEtalePullback f :=
  MorphismProperty.Over.pullbackComp f g

/-- Base change along `f` is continuous for the étale topologies of algebraic spaces. -/
instance spacesEtalePullback_isContinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (spacesEtalePullback f).IsContinuous (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
