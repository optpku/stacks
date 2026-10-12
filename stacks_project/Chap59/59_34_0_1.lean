/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/- 59.34.0.1: For a scheme morphism f : X ⟶ Y, the induced functor
    u : Y.Etale ⥤ X.Etale sends V/Y to X ×_Y V/X. -/
@[stacks 04I1] #check (AlgebraicGeometry.Scheme.smallEtalePullback f : Y.Etale ⥤ X.Etale)
