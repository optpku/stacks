/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization

/-!
# Injectivity along small-to-big étale relocalization

Inverse image of abelian sheaves along `i_f`, and restriction to the small
étale site, preserve injective objects and K-injective complexes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

/-- Abelian-sheaf relocalization along a morphism of algebraic spaces preserves
injective objects. -/
noncomputable instance relocalization_preservesInjectiveObjects
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}] :
    (inverseImage f).PreservesInjectiveObjects :=
  sorry

/-- Inverse image of an injective abelian sheaf along `i_f` is injective. -/
theorem relocalization_preservesInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    (I : Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})
    [Injective I] :
    Injective ((inverseImage f).obj I) :=
  sorry

/-- Restriction of an injective abelian sheaf from `(Spaces/X)_étale` to `X_étale`
is injective. -/
theorem relocalization_restriction_preservesInjective
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    (I : Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})
    [Injective I] :
    Injective ((inverseImage (𝟙 X)).obj I) :=
  sorry

/-- Inverse image of a K-injective complex of abelian sheaves along `i_f` is
K-injective. -/
theorem relocalization_preservesKInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    (I : CochainComplex (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective (((inverseImage f).mapHomologicalComplex (up ℤ)).obj I) :=
  sorry

attribute [instance] relocalization_preservesKInjective

/-- Restriction of a K-injective complex from `(Spaces/X)_étale` to `X_étale` is
K-injective. -/
theorem relocalization_restriction_preservesKInjective
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    (I : CochainComplex (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((inverseImage (𝟙 X)).mapHomologicalComplex (up ℤ)).obj I) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end
