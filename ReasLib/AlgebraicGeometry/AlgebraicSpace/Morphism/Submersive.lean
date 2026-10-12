/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuotientMap

/-!
# Submersive morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is submersive when its map on points is a
quotient map for canonical point-space topologies. -/
def Submersive {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  pointsIsQuotientMap f

/-- A morphism of algebraic spaces is universally submersive when every base
change induces a quotient map on points. -/
def UniversallySubmersive {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  universally pointsIsQuotientMap f

end AlgebraicGeometry.AlgebraicSpace
