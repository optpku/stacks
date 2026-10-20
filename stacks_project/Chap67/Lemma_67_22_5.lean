/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_22_5_EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.22.5: An étale-local property of morphisms of scheme germs holds on every
étale scheme square through a fixed point if and only if it holds on some such square.
For spaces represented by schemes, these conditions are equivalent to the property on
the induced germ morphism. -/
@[stacks 04NC] #check
  (AlgebraicGeometry.AlgebraicSpace.forallEtaleSquareAt_iff_existsEtaleSquareAt :
    ∀ {S : Scheme.{u}} {Q : MorphismProperty Scheme.Germ.{u}}
      (_hQ : Scheme.Germ.MorphismProperty.IsEtaleLocal Q)
      {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X),
      forallEtaleSquareAt Q f x ↔ existsEtaleSquareAt Q f x)

#check (AlgebraicGeometry.AlgebraicSpace.existsEtaleSquareAt_ofOverMap_iff :
  ∀ {S : Scheme.{u}} {Q : MorphismProperty Scheme.Germ.{u}}
    (_hQ : Scheme.Germ.MorphismProperty.IsEtaleLocal Q)
    {U V : Over S} (h : U ⟶ V) (u : U.left),
    existsEtaleSquareAt Q (ofOverMap h) (ofOver.pointsEquiv U u) ↔
      Q (ofOverGermHom h u))

#check (AlgebraicGeometry.AlgebraicSpace.forallEtaleSquareAt_ofOverMap_iff :
  ∀ {S : Scheme.{u}} {Q : MorphismProperty Scheme.Germ.{u}}
    (_hQ : Scheme.Germ.MorphismProperty.IsEtaleLocal Q)
    {U V : Over S} (h : U ⟶ V) (u : U.left),
    forallEtaleSquareAt Q (ofOverMap h) (ofOver.pointsEquiv U u) ↔
      Q (ofOverGermHom h u))

end AlgebraicGeometry.AlgebraicSpace
