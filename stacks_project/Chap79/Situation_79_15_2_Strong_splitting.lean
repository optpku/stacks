/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom.FiniteType

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The set of arrows of a groupoid scheme with source and target equal to a given object
point. -/
def stabilizerFiber {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) : Set G.R.left :=
  G.s.left ⁻¹' ({u} : Set G.U.left) ∩ G.t.left ⁻¹' ({u} : Set G.U.left)

/-- Membership in the equalizer set of source and target at an object point. -/
theorem mem_stabilizerFiber {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    (r : G.R.left) :
    r ∈ stabilizerFiber G u ↔ G.s.left r = u ∧ G.t.left r = u := sorry

/-- Situation 79.15.2 (Strong splitting): standing hypotheses on a pointed groupoid scheme
`(U, R, s, t, c)` over a scheme `S` at a point `u` of `U`. -/
@[stacks 04RL]
class StrongSplitting {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) : Prop where
  /-- The source map is separated. -/
  [s_isSeparated : IsSeparated G.s.left]
  /-- The target map is separated. -/
  [t_isSeparated : IsSeparated G.t.left]
  /-- The source map is locally of finite type. -/
  [s_locallyOfFiniteType : LocallyOfFiniteType G.s.left]
  /-- The target map is locally of finite type. -/
  [t_locallyOfFiniteType : LocallyOfFiniteType G.t.left]
  /-- The equalizer set `{r | s(r) = u ∧ t(r) = u}` is finite. -/
  finite_stabilizerFiber : (stabilizerFiber G u).Finite
  /-- The source map is quasi-finite at every point of the equalizer set. -/
  s_quasiFiniteAt_stabilizer :
    ∀ r ∈ stabilizerFiber G u, QuasiFiniteAt G.s.left r

namespace StrongSplitting

/-- Pack separatedness and local finite type of `s` and `t` together with finiteness of the
equalizer set and source quasi-finiteness on that set. -/
theorem of {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [IsSeparated G.s.left] [IsSeparated G.t.left]
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
    (hfin : (stabilizerFiber G u).Finite)
    (hqf : ∀ r ∈ stabilizerFiber G u, QuasiFiniteAt G.s.left r) :
    StrongSplitting G u where
  finite_stabilizerFiber := hfin
  s_quasiFiniteAt_stabilizer := hqf

/-- The strong-splitting situation is the conjunction of separatedness and local finite type of
`s` and `t`, finiteness of the equalizer set at `u`, and source quasi-finiteness on that set. -/
theorem iff {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    StrongSplitting G u ↔
      IsSeparated G.s.left ∧ IsSeparated G.t.left ∧
        LocallyOfFiniteType G.s.left ∧ LocallyOfFiniteType G.t.left ∧
          (stabilizerFiber G u).Finite ∧
            ∀ r ∈ stabilizerFiber G u, QuasiFiniteAt G.s.left r := sorry

/-- Finite source fibre `s ⁻¹' {u}` implies the equalizer-set finiteness and source
quasi-finiteness conditions of the strong-splitting situation. -/
theorem of_finite_sourceFiber {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [IsSeparated G.s.left] [IsSeparated G.t.left]
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
    (hfin : Set.Finite (G.s.left ⁻¹' ({u} : Set G.U.left))) :
    StrongSplitting G u := sorry

end StrongSplitting

end AlgebraicGeometry.GroupoidScheme
