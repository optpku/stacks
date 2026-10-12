/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.GroupScheme.Action.Module.Quasicoherent.Pullback
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory

variable {S : Scheme.{u}} (G : Grp (Over S))
  {X Y : Mod (Over S) G.X} (f : Y ⟶ X)

/- Lemma 39.12.2: The rule `(F, α) ↦ (f⁎F, (1_G × f)⁎α)` defines a functor
from `G`-equivariant quasi-coherent modules on `X` to those on `Y`. -/
@[stacks 03LG] #check
  (AlgebraicGeometry.Scheme.QCoh.Equivariant.pullback G f :
    AlgebraicGeometry.Scheme.QCoh.Equivariant G X ⥤
      AlgebraicGeometry.Scheme.QCoh.Equivariant G Y)
