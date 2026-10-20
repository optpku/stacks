module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.CategoryTheory.Adjunction.Exactness
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import ReasLib.Topology.Sheaves.Abelian

/-!
# Exactness of pullback for abelian sheaves

This module records the exactness of inverse image for sheaves of abelian groups on topological
spaces, independently of any ringed-space specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

noncomputable section

universe u

namespace TopCat.Sheaf

/-- Inverse image of sheaves of abelian groups along a continuous map is exact. -/
@[stacks 01AJ "(3)"]
theorem pullback_addCommGrp_exact
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    exactFunctor (Y.Sheaf AddCommGrpCat.{u}) (X.Sheaf AddCommGrpCat.{u})
      (pullback AddCommGrpCat.{u} f) := sorry

/-- Inverse image of abelian sheaves is additive, available to typeclass search. -/
@[stacks 01AJ "(3), additive inverse image"]
noncomputable instance pullbackAddCommGrpAdditive
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (pullback AddCommGrpCat.{u} f).Additive := sorry

/-- Inverse image of abelian sheaves preserves finite limits, available to typeclass search. -/
@[stacks 01AJ "(3), finite limits"]
noncomputable instance pullbackAddCommGrpPreservesFiniteLimits
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (pullback AddCommGrpCat.{u} f) := sorry

/-- Inverse image of abelian sheaves preserves finite colimits, available to typeclass search. -/
@[stacks 01AJ "(3), finite colimits"]
noncomputable instance pullbackAddCommGrpPreservesFiniteColimits
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pullback AddCommGrpCat.{u} f) := sorry

/-- Inverse image of abelian sheaves, bundled as an exact functor. -/
@[stacks 01AJ "(3), bundled exact inverse image"]
noncomputable abbrev exactPullback
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Y.Sheaf AddCommGrpCat.{u} ⥤ₑ X.Sheaf AddCommGrpCat.{u} :=
  ExactFunctor.of (pullback AddCommGrpCat.{u} f)

end TopCat.Sheaf
