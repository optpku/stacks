/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Gerbe
import StacksCheckRecall

/-!
# When a morphism of quotient stacks is a gerbe

This file records the sufficient criterion that `[f] : [U/R] ⟶ [U'/R']` exhibits
`[U/R]` as a gerbe over `[U'/R']` when the object map and the restriction
comparison of arrow spaces are surjective as maps of fppf sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/- Lemma 78.27.1. Notation and assumption as in Lemma 78.21.1. The morphism of
quotient stacks `[f] : [U/R] ⟶ [U'/R']` turns `[U/R]` into a gerbe over `[U'/R']`
if `f.obj : U ⟶ U'` and `f.restrictionArrow : R ⟶ R'|_U` are surjective maps of
fppf sheaves. Here `R'|_U` is the restriction of `R'` to `U` via `f.obj : U ⟶ U'`,
i.e. the arrow space of `H.pullback f.obj`. -/
@[stacks 06PE] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.quotientStackMap_isGerbeMorphism :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : GroupoidAlgebraicSpace.Hom G H)
    (h_obj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f.obj.left)
    (h_arrow : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      f.restrictionArrow.left),
    CartesianBasedFunctor.IsGerbeMorphism (Scheme.fppfTopology.over S) f.quotientStackMap)
