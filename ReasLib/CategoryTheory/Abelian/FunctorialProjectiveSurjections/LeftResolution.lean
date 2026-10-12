/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.LeftResolution.Basic
public import ReasLib.CategoryTheory.Abelian.FunctorialProjectiveSurjections.Definition

@[expose] public section

/-!
# Projective Surjections from Left Resolutions

This module connects a left resolution by projective objects with the reusable
`HasFunctorialProjectiveSurjections` interface.
-/

namespace CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C] [HasFunctorialProjectiveSurjections C]

/-- A functorial projective-surjection choice determines a left resolution by projective
objects. -/
@[reducible]
def HasFunctorialProjectiveSurjections.toLeftResolution :
    Abelian.LeftResolution (ObjectProperty.ι (isProjective C)) where
  F := (isProjective C).lift HasFunctorialProjectiveSurjections.overFunctor
    HasFunctorialProjectiveSurjections.over_projective
  π := HasFunctorialProjectiveSurjections.πNatTrans
  epi_π_app _ := sorry

end

namespace Abelian.LeftResolution

variable {C : Type u} [Category.{v} C]

/-- A left resolution by projective objects supplies functorial projective surjections. -/
@[reducible]
noncomputable def hasFunctorialProjectiveSurjections
    (Λ : LeftResolution (ObjectProperty.ι (isProjective C))) :
    HasFunctorialProjectiveSurjections C where
  overFunctor := Λ.F ⋙ ObjectProperty.ι (isProjective C)
  πNatTrans := Λ.π
  epi_obj _ := sorry
  projective_obj _ := sorry

/-- A left resolution by projective objects provides enough projectives. -/
theorem toEnoughProjectives
    (Λ : LeftResolution (ObjectProperty.ι (isProjective C))) :
    EnoughProjectives C := sorry

end Abelian.LeftResolution

end CategoryTheory
