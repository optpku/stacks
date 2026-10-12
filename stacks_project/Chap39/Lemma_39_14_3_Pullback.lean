/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Pullback

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

variable {S : Scheme.{u}} {G H : GroupoidScheme S} (f : GroupoidScheme.Hom G H)

/- Compatibility bridge for pullback of equivariant quasi-coherent modules along a
groupoid-scheme morphism. -/
#check (AlgebraicGeometry.GroupoidScheme.QCoh.pullback f : H.QCoh ⥤ G.QCoh)
