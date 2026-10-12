/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Action.Module.Quasicoherent.Pullback
public import stacks_project.Chap39.Definition_39_12_1_Equivariant

universe u

open AlgebraicGeometry CategoryTheory

variable {S : Scheme.{u}} (G : Grp (Over S))
  {X Y : Mod (Over S) G.X} (f : Y ⟶ X)

/- Compatibility check for equivariant pullback along an equivariant morphism. -/
#check
  (AlgebraicGeometry.Scheme.QCoh.Equivariant.pullback G f :
    AlgebraicGeometry.Scheme.QCoh.Equivariant G X ⥤
      AlgebraicGeometry.Scheme.QCoh.Equivariant G Y)
