/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import stacks_project.Chap78.Example_78_7_6_Constant_group_algebraic_space_Group
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OfScheme
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Quotient

/-!
# Quotient stacks of group scheme actions

The quotient and classifying stack constructions are supplied by their shared
mathematical owners. The groupoid conversion name and source-facing prerequisite
imports remain available for existing consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A groupoid scheme over `S`, regarded as a groupoid in algebraic spaces over `S`. -/
abbrev ofGroupoidScheme {S : Scheme.{u}} (G : GroupoidScheme S) :
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))) :=
  ofScheme G

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.ofScheme :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.ofScheme_U :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
    (ofScheme G).U.left = ofOver G.U)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.ofScheme_R :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
    (ofScheme G).R.left = ofOver G.R)

end AlgebraicGeometry.GroupoidAlgebraicSpace

#check (AlgebraicGeometry.GroupScheme.trivialAction :
    ∀ {S : Scheme.{u}} (G : GroupScheme S), GroupScheme.Action G)

#check (AlgebraicGeometry.GroupScheme.trivialAction_X :
    ∀ {S : Scheme.{u}} (G : GroupScheme S),
    (GroupScheme.trivialAction G).X = 𝟙_ (Over S))

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.quotient :
    ∀ {k : Type u} [Field k] (G : GroupScheme (Spec (.of k)))
    (X : GroupScheme.Action G), GroupoidsOver (Spec (.of k)))

#check (AlgebraicGeometry.AlgebraicStack.quotient_spec :
    ∀ {k : Type u} [Field k] (G : GroupScheme (Spec (.of k)))
    (X : GroupScheme.Action G),
    quotient G X =
      GroupoidAlgebraicSpace.SmallQuotient.quotientStack
        (GroupoidAlgebraicSpace.ofScheme (GroupoidScheme.ofAction G X)))

#check (AlgebraicGeometry.AlgebraicStack.classifying :
    ∀ {k : Type u} [Field k] (G : GroupScheme (Spec (.of k))),
    GroupoidsOver (Spec (.of k)))

#check (AlgebraicGeometry.AlgebraicStack.classifying_spec :
    ∀ {k : Type u} [Field k] (G : GroupScheme (Spec (.of k))),
    classifying G = quotient G (GroupScheme.trivialAction G))

#check (AlgebraicGeometry.AlgebraicStack.instAlgebraicStack_quotient :
    ∀ {k : Type u} [Field k] (G : GroupScheme (Spec (.of k)))
    (X : GroupScheme.Action G) [Algebraic X.X] [Algebraic G.X],
    AlgebraicStack (quotient G X))

#check (AlgebraicGeometry.AlgebraicStack.instIsLocallyNoetherian_quotient :
    ∀ {k : Type u} [Field k] (G : GroupScheme (Spec (.of k)))
    (X : GroupScheme.Action G) [Algebraic X.X] [Algebraic G.X],
    IsLocallyNoetherian (quotient G X))

#check (AlgebraicGeometry.AlgebraicStack.instAlgebraicStack_classifying :
    ∀ {k : Type u} [Field k] (G : GroupScheme (Spec (.of k))) [Algebraic G.X],
    AlgebraicStack (classifying G))

#check (AlgebraicGeometry.AlgebraicStack.instIsLocallyNoetherian_classifying :
    ∀ {k : Type u} [Field k] (G : GroupScheme (Spec (.of k))) [Algebraic G.X],
    IsLocallyNoetherian (classifying G))

end AlgebraicGeometry.AlgebraicStack
