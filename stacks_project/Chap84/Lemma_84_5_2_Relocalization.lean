/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap73.Definition_73_4_1_Precoverage

/-!
# Small-to-big étale relocalization of algebraic spaces

The functor `i_f` sends an étale scheme over an algebraic space `Y` to the same
object of `Over X` along a morphism `f : Y ⟶ X`. Inverse image of abelian
sheaves is precomposition with this functor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

/-- The big étale topology on `Over X`, i.e. `(Spaces/X)_étale`. -/
abbrev overEtaleTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    GrothendieckTopology (Over X) :=
  (etalePrecoverage : Precoverage (AlgebraicSpace S)).toGrothendieck.over X

/-- The big étale topology on `Over X` is the slice of the étale Grothendieck
topology of algebraic spaces over `S`. -/
theorem overEtaleTopology_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    overEtaleTopology X =
      (etalePrecoverage : Precoverage (AlgebraicSpace S)).toGrothendieck.over X :=
  sorry

/-- The relocalization functor from the small étale site of `Y` to the big
étale slice site over `X`. -/
abbrev relocalizationFunctor {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    smallEtaleSite Y ⥤ Over X :=
  smallEtaleInclusion Y ⋙ MorphismProperty.Over.forget (@Etale S) ⊤ Y ⋙ Over.map f

/-- The relocalization functor is continuous for the small-to-big étale topologies. -/
instance relocalizationFunctor_isContinuous {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    Functor.IsContinuous (relocalizationFunctor f) (smallEtaleTopology Y)
      (overEtaleTopology X) :=
  sorry

/-- The relocalization functor is cocontinuous for the small-to-big étale topologies. -/
instance relocalizationFunctor_isCocontinuous {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    Functor.IsCocontinuous (relocalizationFunctor f) (smallEtaleTopology Y)
      (overEtaleTopology X) :=
  sorry

/-- Inverse image of abelian sheaves along étale relocalization. -/
abbrev inverseImage {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  (relocalizationFunctor f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology Y) (overEtaleTopology X)

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end
