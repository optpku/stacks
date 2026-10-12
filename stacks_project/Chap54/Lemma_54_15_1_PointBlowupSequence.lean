/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.FinitePointSequence

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

#check (AlgebraicGeometry.Scheme.PointBlowupSequence :
  Scheme.{u} → Scheme.{u} → Type (u + 1))

end AlgebraicGeometry.Scheme
