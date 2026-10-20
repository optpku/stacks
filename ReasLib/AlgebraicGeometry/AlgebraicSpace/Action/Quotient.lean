/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Restrict
public import ReasLib.CategoryTheory.Monoidal.Cartesian.FreeAction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient

/-! Algebraic-space quotients and torsors associated to free group actions. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G)

/-- A free action of a group algebraic space yields an equivalence relation on the
associated action groupoid. -/
theorem isEquivalenceRelation_ofAction [Mod.IsFree X] :
    IsEquivalenceRelation (ofAction G X).t (ofAction G X).s := sorry

/-- Flatness of `G ⟶ B` implies flatness of the action-groupoid source
`(g, x) ↦ x`. -/
theorem flat_ofAction_s [AlgebraicSpace.Flat G.X.hom] :
    AlgebraicSpace.Flat (ofAction G X).s.left := sorry

/-- Flatness of `G ⟶ B` implies flatness of the action-groupoid target
`(g, x) ↦ a(g, x)`, by inversion. -/
theorem flat_ofAction_t [AlgebraicSpace.Flat G.X.hom] :
    AlgebraicSpace.Flat (ofAction G X).t.left := sorry

/-- Local finite presentation of `G ⟶ B` implies local finite presentation of the
action-groupoid source `(g, x) ↦ x`. -/
theorem locallyOfFinitePresentation_ofAction_s
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    AlgebraicSpace.LocallyOfFinitePresentation (ofAction G X).s.left := sorry

/-- Local finite presentation of `G ⟶ B` implies local finite presentation of the
action-groupoid target `(g, x) ↦ a(g, x)`, by inversion. -/
theorem locallyOfFinitePresentation_ofAction_t
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    AlgebraicSpace.LocallyOfFinitePresentation (ofAction G X).t.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace.Action

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable (G : GroupAlgebraicSpace B) (X : Action G)

/-- A free action of a flat, locally finitely presented group algebraic space has
an algebraic-space fppf quotient. -/
theorem hasAlgebraicSpaceQuotient_of_isFree [Mod.IsFree X]
    [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    (GroupoidAlgebraicSpace.ofAction G X).HasAlgebraicSpaceQuotient := sorry

/-- A morphism representing the quotient of a free action of a flat, locally
finitely presented group algebraic space is surjective, flat, and locally of finite
presentation. -/
theorem quotientHom_surjective_flat_locallyOfFinitePresentation
    {F : AlgebraicSpace S} (q : X.X.left ⟶ F)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q)
    [Mod.IsFree X] [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom]
    [IsIso ((GroupoidAlgebraicSpace.ofAction G X).toPreRelation.quotientSheafDesc q h_eq)] :
    AlgebraicSpace.Surjective q ∧ AlgebraicSpace.Flat q ∧
      AlgebraicSpace.LocallyOfFinitePresentation q :=
  @GroupoidAlgebraicSpace.quotientHom_surjective_flat_locallyOfFinitePresentation
    S B (GroupoidAlgebraicSpace.ofAction G X) F q h_eq
    (GroupoidAlgebraicSpace.isEquivalenceRelation_ofAction G X)
    (GroupoidAlgebraicSpace.flat_ofAction_s G X)
    (GroupoidAlgebraicSpace.flat_ofAction_t G X)
    (GroupoidAlgebraicSpace.locallyOfFinitePresentation_ofAction_s G X)
    (GroupoidAlgebraicSpace.locallyOfFinitePresentation_ofAction_t G X)
    inferInstance

/-- The canonical comparison from a free action relation to the kernel pair of a
representing quotient morphism is an isomorphism for a flat, locally finitely
presented group algebraic space. -/
theorem kernelPairLift_isIso
    {F : AlgebraicSpace S} (q : X.X.left ⟶ F)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q)
    [Mod.IsFree X] [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom]
    [IsIso ((GroupoidAlgebraicSpace.ofAction G X).toPreRelation.quotientSheafDesc q h_eq)] :
    IsIso ((GroupoidAlgebraicSpace.ofAction G X).toPreRelation.kernelPairLift q h_eq) :=
  sorry

/-- The action restricted to an algebraic-space quotient of a free action of a
flat, locally finitely presented group algebraic space is an fppf torsor. -/
theorem isStandardTorsor_over_quotient
    {F : AlgebraicSpace S} (q : X.X.left ⟶ F)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q)
    [Mod.IsFree X] [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom]
    [IsIso ((GroupoidAlgebraicSpace.ofAction G X).toPreRelation.quotientSheafDesc q h_eq)]
    (f : F ⟶ B) (hq : q ≫ f = X.X.hom) :
    IsStandardTorsor (GroupAlgebraicSpace.baseChange G f)
      (restrictTo G X f q hq h_eq) StandardTopology.fppf := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Action
