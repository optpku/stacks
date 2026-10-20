/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientPresheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.Representability
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Covering properties of groupoid quotients in algebraic spaces

A quotient map for an equivalence-relation groupoid with flat, locally finitely
presented source and target is surjective, flat, and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A morphism identifying its target with the canonical fppf quotient of an
equivalence-relation groupoid whose source and target are flat and locally of finite
presentation is surjective, flat, and locally of finite presentation. -/
theorem quotientHom_surjective_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {F : AlgebraicSpace S} (q : G.U.left ⟶ F)
    (h_equalizes : G.toPreRelation.t.left ≫ q = G.toPreRelation.s.left ≫ q)
    [IsEquivalenceRelation G.t G.s]
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.t.left]
    [IsIso (G.toPreRelation.quotientSheafDesc q h_equalizes)] :
    AlgebraicSpace.Surjective q ∧ AlgebraicSpace.Flat q ∧
      AlgebraicSpace.LocallyOfFinitePresentation q := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace

/-- A flat locally finitely presented equivalence-relation groupoid in algebraic spaces has
an algebraic-space quotient: an fppf sheaf locally bijective to its quotient presheaf is
an algebraic space. -/
@[stacks 04S6]
theorem IsAlgebraicSpace.of_groupoidAlgebraicSpace {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [IsEquivalenceRelation G.t G.s] [Flat G.s.left] [Flat G.t.left]
    [LocallyOfFinitePresentation G.s.left] [LocallyOfFinitePresentation G.t.left]
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (η : G.toPreRelation.quotientPresheaf ⟶ F)
    (hη_inj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (hη_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η) :
    IsAlgebraicSpace F :=
  sorry

/-- A flat locally finitely presented equivalence-relation groupoid scheme has an
algebraic-space quotient: an fppf sheaf locally bijective to its quotient presheaf is
an algebraic space. -/
@[stacks 04S6]
theorem IsAlgebraicSpace.of_groupoidScheme {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsEquivalenceRelation G.t G.s] [AlgebraicGeometry.Flat G.s.left]
    [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left]
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (η : G.toPreRelation.quotientPresheaf ⟶ F)
    (hη_inj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (hη_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η) :
    IsAlgebraicSpace F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
