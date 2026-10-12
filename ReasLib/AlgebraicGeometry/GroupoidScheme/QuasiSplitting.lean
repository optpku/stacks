/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Standing hypotheses for a groupoid scheme at a point: its source and target maps
are separated and locally of finite type, and its source is quasi-finite at the
identity arrow of the point. -/
class IsQuasiSplittingSituation {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    Prop where
  /-- The source map is separated. -/
  [source_isSeparated : IsSeparated G.s.left]
  /-- The target map is separated. -/
  [target_isSeparated : IsSeparated G.t.left]
  /-- The source map is locally of finite type. -/
  [source_locallyOfFiniteType : LocallyOfFiniteType G.s.left]
  /-- The target map is locally of finite type. -/
  [target_locallyOfFiniteType : LocallyOfFiniteType G.t.left]
  /-- The source map is quasi-finite at the identity arrow of `u`. -/
  source_quasiFiniteAt_identity : G.s.left.QuasiFiniteAt (G.e.left u)

namespace IsQuasiSplittingSituation

/-- Construct the quasi-splitting situation property from its geometric hypotheses. -/
theorem of {S : Scheme.{u}} {G : GroupoidScheme S} {u : G.U.left}
    [IsSeparated G.s.left] [IsSeparated G.t.left]
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
    (h : G.s.left.QuasiFiniteAt (G.e.left u)) :
    IsQuasiSplittingSituation G u := sorry

end IsQuasiSplittingSituation

/-- The quasi-splitting situation property is equivalent to its five geometric hypotheses. -/
theorem isQuasiSplittingSituation_iff {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) :
    IsQuasiSplittingSituation G u ↔
      IsSeparated G.s.left ∧ IsSeparated G.t.left ∧
        LocallyOfFiniteType G.s.left ∧ LocallyOfFiniteType G.t.left ∧
          G.s.left.QuasiFiniteAt (G.e.left u) := sorry

/-- The discrete groupoid scheme satisfies the quasi-splitting hypotheses at every point. -/
theorem isQuasiSplittingSituation_discrete {S : Scheme.{u}} (U : Over S)
    (u : U.left) : IsQuasiSplittingSituation (discrete U) u := sorry

end AlgebraicGeometry.GroupoidScheme
