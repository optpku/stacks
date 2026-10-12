/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineFamily

@[expose] public section

universe u

namespace AlgebraicGeometry

#check (AlgebraicGeometry.ProjectiveLineFamily.space :
  {S : Scheme.{u}} → CategoryTheory.Over S → Scheme.{u})

end AlgebraicGeometry
