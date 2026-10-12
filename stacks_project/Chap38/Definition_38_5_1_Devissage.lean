/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageOver

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.Modules.CompleteDevissageOver :
  {S X : Scheme.{u}} → (f : X ⟶ S) → (F : X.Modules) →
    [LocallyOfFiniteType f] → [F.IsQuasicoherent] → [F.IsFiniteType] →
      (s : S) → Type (u + 1))
