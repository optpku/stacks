/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction
import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Presentation
import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Points
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 39.18.1 (1): restriction along `g : U' ⟶ U` gives a groupoid scheme whose
composition is induced canonically from the original composition. -/
@[stacks 02VB] #check
  (AlgebraicGeometry.GroupoidScheme.pullback :
    {S : AlgebraicGeometry.Scheme.{u}} →
      (G : AlgebraicGeometry.GroupoidScheme S) →
      {U' : Over S} → (g : U' ⟶ G.U) →
        AlgebraicGeometry.GroupoidScheme S)

/- Companion recall: `AlgebraicGeometry.GroupoidScheme.pullback_c G g` identifies the
restricted composition with the canonical pullback composition. -/
#check
  (AlgebraicGeometry.GroupoidScheme.pullback_c :
    {S : AlgebraicGeometry.Scheme.{u}} →
      (G : AlgebraicGeometry.GroupoidScheme S) →
      {U' : Over S} → (g : U' ⟶ G.U) →
        (AlgebraicGeometry.GroupoidScheme.pullback G g).c =
          AlgebraicGeometry.GroupoidScheme.pullbackComposition G g)

/- Companion recall: the restricted arrow scheme has the iterated fibre-product
presentation from the two displayed pullback squares. -/
#check
  (AlgebraicGeometry.GroupoidScheme.pullbackArrowIso :
    {S : AlgebraicGeometry.Scheme.{u}} →
      (G : AlgebraicGeometry.GroupoidScheme S) →
      {U' : Over S} → (g : U' ⟶ G.U) →
        (G.toPreRelation.pullback g).left ≅
          AlgebraicGeometry.GroupoidScheme.iteratedPullbackArrows G g)

/- Lemma 39.18.1 (2): the projections from the restricted object and arrow schemes define
a morphism to the original groupoid scheme. -/
@[stacks 02VB] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackHom :
    {S : AlgebraicGeometry.Scheme.{u}} →
      (G : AlgebraicGeometry.GroupoidScheme S) →
      {U' : Over S} → (g : U' ⟶ G.U) →
        AlgebraicGeometry.GroupoidScheme.Hom
          (AlgebraicGeometry.GroupoidScheme.pullback G g) G)

/- Lemma 39.18.1 (3): on every scheme of points, the canonical functor identifies with the
restriction of the original groupoid along the induced object map. -/
@[stacks 02VB] #check
  (AlgebraicGeometry.GroupoidScheme.pointsPullbackEquivalence_comp :
    {S : AlgebraicGeometry.Scheme.{u}} →
      (G : AlgebraicGeometry.GroupoidScheme S) →
      {U' : Over S} → (g : U' ⟶ G.U) → (T : Over S) →
        (AlgebraicGeometry.GroupoidScheme.pointsPullbackEquivalence G g T).functor ⋙
            CategoryTheory.inducedFunctor
              (AlgebraicGeometry.GroupoidScheme.restrictionObjectMap G g T) =
          (AlgebraicGeometry.GroupoidScheme.pullbackHom G g).mapPoints.app
            (Opposite.op T))
