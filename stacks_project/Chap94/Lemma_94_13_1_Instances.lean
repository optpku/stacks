/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_2_DeligneMumford

/-!
# Representable groupoid fibrations as Deligne-Mumford stacks

A category fibred in groupoids over `(Sch/S)_fppf` that is representable by an
algebraic space is a Deligne-Mumford stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace DeligneMumfordStack

/-- A category fibred in groupoids over `(Sch/S)_fppf` that is representable by
an algebraic space is a Deligne-Mumford stack. -/
theorem of_isRepresentableByAlgebraicSpace {S : Scheme.{u}}
    {X : GroupoidsOver S} (hX : IsRepresentableByAlgebraicSpace X) :
    DeligneMumfordStack X := sorry

end DeligneMumfordStack

end AlgebraicGeometry
