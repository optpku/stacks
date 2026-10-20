/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction

open CategoryTheory

universe u

/- Definition 39.18.2: the morphism `AlgebraicGeometry.GroupoidScheme.pullbackHom G g`
is the canonical morphism from the restricted groupoid scheme `G.pullback g` to `G`. -/
@[stacks 02VC] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackHom :
    {S : AlgebraicGeometry.Scheme.{u}} →
      (G : AlgebraicGeometry.GroupoidScheme S) →
      {U' : Over S} → (g : U' ⟶ G.U) →
      AlgebraicGeometry.GroupoidScheme.Hom
        (AlgebraicGeometry.GroupoidScheme.pullback G g) G)

/- Companion recall: `pullbackHom G g` uses `g` on objects and the canonical pullback
projection on arrows. -/
#check
  (AlgebraicGeometry.GroupoidScheme.pullbackHom_spec :
    {S : AlgebraicGeometry.Scheme.{u}} →
      (G : AlgebraicGeometry.GroupoidScheme S) →
      {U' : Over S} → (g : U' ⟶ G.U) →
      (AlgebraicGeometry.GroupoidScheme.pullbackHom G g).obj = g ∧
        (AlgebraicGeometry.GroupoidScheme.pullbackHom G g).arrow =
          AlgebraicGeometry.GroupoidScheme.pullbackArrow G g)

/- Companion recall: the arrow scheme of `G.pullback g` is the pulled-back relation object
corresponding to the notation `R|_{U'}`. -/
#check
  (AlgebraicGeometry.GroupoidScheme.pullback_R :
    {S : AlgebraicGeometry.Scheme.{u}} →
      (G : AlgebraicGeometry.GroupoidScheme S) →
      {U' : Over S} → (g : U' ⟶ G.U) →
      (AlgebraicGeometry.GroupoidScheme.pullback G g).R =
        (G.toPreRelation.pullback g).left)
