/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 78.17.2: the morphism `AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackHom G g`
is the restriction of the groupoid in algebraic spaces `G` along `g : U' ⟶ U` over `B`.
The source sometimes writes `R' = R|_{U'}` for `(pullback G g).R`. -/
@[stacks 044C] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackHom :
    {S : AlgebraicGeometry.Scheme.{u}} → {B : AlgebraicGeometry.AlgebraicSpace S} →
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      {U' : Over B} → (g : U' ⟶ G.U) →
        AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
          (AlgebraicGeometry.GroupoidAlgebraicSpace.pullback G g) G)

/- Companion recall: `pullbackHom G g` uses `g` on objects and the canonical pullback
projection on arrows. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackHom_spec :
    {S : AlgebraicGeometry.Scheme.{u}} → {B : AlgebraicGeometry.AlgebraicSpace S} →
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      {U' : Over B} → (g : U' ⟶ G.U) →
      (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackHom G g).obj = g ∧
        (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackHom G g).arrow =
          AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrow G g)

/- Companion recall: the arrow space of `G.pullback g` is the pulled-back relation object
corresponding to the notation `R|_{U'}`. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullback_R :
    {S : AlgebraicGeometry.Scheme.{u}} → {B : AlgebraicGeometry.AlgebraicSpace S} →
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      {U' : Over B} → (g : U' ⟶ G.U) →
      (AlgebraicGeometry.GroupoidAlgebraicSpace.pullback G g).R =
        (G.toPreRelation.pullback g).left)
