/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.StalkFlatness

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A module sheaf is flat over an algebraic space if every étale scheme square realizes it
as a module whose stalks are flat over the target chart's local rings. -/
def FlatOver (F : Modules X) (f : X ⟶ Y) : Prop :=
  ∀ square : Square f,
    Scheme.Modules.IsStalkFlatOver ((toScheme square.source).obj F) square.map.left

/-- Relative flatness is equivalent to stalkwise relative flatness on every étale scheme
square. -/
theorem flatOver_iff (F : Modules X) (f : X ⟶ Y) :
    FlatOver F f ↔ ∀ square : Square f,
      Scheme.Modules.IsStalkFlatOver ((toScheme square.source).obj F) square.map.left := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules
