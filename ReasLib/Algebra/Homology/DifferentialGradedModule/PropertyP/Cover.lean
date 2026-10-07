module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.HomologyMaps
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP

/-!
# Two-step property P covers
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DifferentialGradedModule.PropertyP

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/-- A two-step property P cover records an admissible extension of two coproducts of shifts of
the regular module, together with a map which is epic on the underlying graded module and on
cycles. -/
@[stacks 09KN "two-step property-P covers"]
structure Cover (M : DifferentialGradedModule.{u, v} A) where
  /-- The admissible two-step presentation of the source. -/
  sequence : ShortComplex (DifferentialGradedModule.{u, v} A)
  /-- The presentation is admissibly short exact. -/
  admissible : DifferentialGradedModule.IsAdmissibleShortExact sequence
  /-- The chosen coproduct-of-shifts presentation of the left term. -/
  leftPiece : Piece A sequence.X₁
  /-- The chosen coproduct-of-shifts presentation of the right term. -/
  rightPiece : Piece A sequence.X₃
  /-- The cover map from the middle term to the target. -/
  π : sequence.X₂ ⟶ M
  /-- The cover is epic after forgetting the differential. -/
  gradedEpi : Epi ((forgetToGraded A).map π)
  /-- The cover is epic on cycles in every degree. -/
  cyclesEpi : Hom.EpiOnCycles π

namespace Cover

/-- The source module of a two-step property P cover. -/
abbrev source {M : DifferentialGradedModule.{u, v} A} (C : Cover A M) :=
  C.sequence.X₂

/-- The left term of a two-step property P cover is a coproduct of shifted regular modules. -/
theorem left_mem {M : DifferentialGradedModule.{u, v} A} (C : Cover A M) :
    IsCoproductOfShifts A C.sequence.X₁ := sorry

/-- The right term of a two-step property P cover is a coproduct of shifted regular modules. -/
theorem right_mem {M : DifferentialGradedModule.{u, v} A} (C : Cover A M) :
    IsCoproductOfShifts A C.sequence.X₃ := sorry

/-- A two-step property P cover is epic in the category of right DG modules. -/
instance πEpi {M : DifferentialGradedModule.{u, v} A} (C : Cover A M) : Epi C.π := sorry

/-- The source of a two-step property P cover has property P. -/
theorem source_hasPropertyP {M : DifferentialGradedModule.{u, v} A} (C : Cover A M) :
    HasPropertyP A C.source := sorry

/-- Lemma 22.20.3 (09KN): every right DG `A`-module admits a two-step property P cover which is
epic both on the underlying graded module and on cycles. -/
@[stacks 09KN]
theorem nonempty (M : DifferentialGradedModule.{u, v} A) : Nonempty (Cover A M) := sorry

end Cover

end DifferentialGradedModule.PropertyP
