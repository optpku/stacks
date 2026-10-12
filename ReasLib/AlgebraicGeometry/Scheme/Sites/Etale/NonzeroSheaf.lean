/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

/-!
# Nonzero étale sheaves vanishing on fields
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- An abelian sheaf on the big étale site vanishes on spectra of fields. -/
def vanishesOnFields (G : Sheaf Scheme.etaleTopology AddCommGrpCat.{u}) : Prop :=
  ∀ (k : Type u) [Field k],
    IsZero (G.obj.obj (op (Spec (CommRingCat.of k))))

/-- Restriction of an abelian étale sheaf along every thickening is an
isomorphism. -/
def iso_map_of_isThickening
    (G : Sheaf Scheme.etaleTopology AddCommGrpCat.{u}) : Prop :=
  ∀ {X X' : Scheme.{u}} (i : X ⟶ X') [IsThickening i], IsIso (G.obj.map i.op)

namespace Scheme

namespace Etale

/-- There exists a nonzero abelian sheaf on the big étale site that vanishes
on spectra of fields, preserves directed affine limits, and sends thickenings
to isomorphisms. -/
theorem exists_nonzero_vanishingOnFields :
    ∃ G : Sheaf Scheme.etaleTopology AddCommGrpCat.{u},
      vanishesOnFields G ∧
        Scheme.PreservesDirectedAffineLimits (G.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u}) ∧
        iso_map_of_isThickening G ∧
        ¬ IsZero G := sorry

end Etale

end Scheme

end AlgebraicGeometry
