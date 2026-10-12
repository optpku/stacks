/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Pullback

/-!
# Comparing source fibres of a groupoid in algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Two arrows from the same algebraic space with equal targets determine source fibres
that are isomorphic over that algebraic space. -/
theorem existsSourceFiberIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    {T : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {r r' : T ⟶ G.R.left} (ht : r ≫ G.t.left = r' ≫ G.t.left) :
    Nonempty
      (Over.mk (pullback.snd G.s.left (r ≫ G.s.left)) ≅
        Over.mk (pullback.snd G.s.left (r' ≫ G.s.left))) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
